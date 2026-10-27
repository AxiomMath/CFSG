module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.Item112

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_mem_sectionCentralizer (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) {x : G}
    (hxA : x ∈ A) (hxcd : x ∉ Subgroup.closure ({c, d} : Set G)) {Z : Subgroup G}
    (hKZ : sec11K L x ≤ Z) {e : G} (he : e ∈ Subgroup.closure ({c, d} : Set G))
    (heZ : e ∈ Late.sectionCentralizer A Z (inSubgroup (aschbacherSolvableCore 3) Z)) :
    e ∈ Subgroup.zpowers c := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  have hcA := h.mem_A
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hd3 : d ^ 3 = 1 := hexp d hdAL.1
  obtain ⟨hxN, hx3, hZ, hQ, hdK⟩ := basic_facts_of_conj h45 h hdL hA hxA hxcd
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe hcA h.ne_one L
      h.mem_thetaComponentsAt
  have hθL : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    hAL.trans (Sec6.normalizer_le_normalizer_theta L)
  have hAK : A ≤ Subgroup.normalizer (sec11K L x : Set G) := by
    intro z hz
    refine GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _ ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hzC : z ∈ Subgroup.normalizer
        ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz x hxA))
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAL hz) y).mp hy1,
        (Subgroup.mem_normalizer_iff.mp hzC y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAL hz) y).mpr hy1,
        (Subgroup.mem_normalizer_iff.mp hzC y).mpr hy2⟩
  set T := sectionCentralizerSubgroup A (sec11K L x) (inSubgroup (aschbacherSolvableCore 3) L)
    hAK hθL with hT
  have heT : e ∈ T :=
    ⟨heZ.1, mem_theta_of_mem_sectionCentralizer_of_le hxN hx3 hQ hZ hKZ (hAK heZ.1) heZ⟩
  have hcsec : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [h.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  have hcT : c ∈ T := ⟨hcA, fun k hk => hcsec.2 k (sec11K_le L x hk)⟩
  have hdT : d ∉ T := by
    rintro ⟨-, hd⟩
    have hd1 := eq_one_of_forall_mem_theta hxN hx3 hQ hZ hdK hd3 hd
    rw [hd1] at hA
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.one_mem _
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a h.a_mem) (hexp c hcA) (hexp a h.a_mem)
    rw [h.card_eq] at h1
    omega
  by_contra hec
  have hcd : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hcA
    · exact hdAL.1
  have hce : Subgroup.closure ({c, e} : Set G) ≤ Subgroup.closure {c, d} := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact he
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have h9 := Sec9.three_mul_card_le_of_le_of_ne hA3 (hce.trans hcd)
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c _)))
    (fun heq => hec (by
      rw [heq]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)))
  rw [Nat.card_zpowers, hc3] at h9
  have h9' := Sec10.card_closure_pair_le (hcomm c hcA d hdAL.1) (hexp c hcA) hd3
  have heq : Subgroup.closure ({c, e} : Set G) = Subgroup.closure {c, d} :=
    Subgroup.eq_of_le_of_card_ge hce (by omega)
  apply hdT
  have hle : Subgroup.closure ({c, e} : Set G) ≤ T := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hcT
    · exact heT
  exact hle (heq ▸ Subgroup.subset_closure (Set.mem_insert_of_mem c rfl))

theorem mem_normalizer_of_conj_mem_zpowers {c g : G} (h : g⁻¹ * c * g ∈ Subgroup.zpowers c) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hg : g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [SetLike.mem_coe, ← conj_zpow, inv_inv]
    exact Subgroup.zpow_mem _ h k
  simpa using Subgroup.inv_mem _ hg

theorem item118_of (h117 : Item117) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) : Item118 := by
  intro G _ _ A c L a R Y h d g hdL hA hgW hgH hb
  have hG := h.toTheoremFourHyp
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hd3 : d ^ 3 = 1 := hexp d hdAL.1
  have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hcA
    · exact hdAL.1
  have hacd : a ∉ Subgroup.closure ({c, d} : Set G) := by
    intro hacd
    have hle : A ≤ Subgroup.closure ({c, d} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact hacd
      · exact Subgroup.subset_closure (by simp)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA d hdAL.1) (hexp c hcA) hd3
    rw [h.card_eq] at h1
    omega
  have hd1 : d ≠ 1 := by
    intro hd1
    rw [hd1] at hA
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.one_mem _
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a haA) (hexp c hcA) (hexp a haA)
    rw [h.card_eq] at h1
    omega
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      have hc : c ∈ Subgroup.closure ({c, a} : Set G) := Subgroup.subset_closure (by simp)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact hc
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr hc hdc
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a haA) (hexp c hcA) (hexp a haA)
    rw [h.card_eq] at h1
    omega
  have hdN : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    (h117 G A c L a R Y h d hdL (Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hdAL.1)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1])).mpr rfl
  have hgd : g * d * g⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (hdN hgW) d).mp (Subgroup.mem_zpowers d)
  have hgd' : g⁻¹ * d * g ∈ Subgroup.zpowers d := by
    have := (Subgroup.mem_normalizer_iff.mp (hdN (Subgroup.inv_mem _ hgW)) d).mp
      (Subgroup.mem_zpowers d)
    rwa [inv_inv] at this
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLg
  have hdLg : d ∈ Lg := ⟨g⁻¹ * d * g, Subgroup.zpowers_le.mpr hdAL.2 hgd', by
    change g * (g⁻¹ * d * g) * g⁻¹ = d
    group⟩
  have hmapcd : (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure {c, d} := by
    have hle : (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.closure {c, d} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hb
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hgd
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hconj : ∀ y ∈ Subgroup.closure ({c, d} : Set G), g⁻¹ * y * g ∈ Subgroup.closure {c, d} := by
    intro y hy
    rw [← hmapcd] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have e : g⁻¹ * (MulAut.conj g).toMonoidHom z * g = z := by
      change g⁻¹ * (g * z * g⁻¹) * g = z
      group
    rw [e]
    exact hz
  set a' := g⁻¹ * a * g with ha'
  have ha'A : a' ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgW) a).mp haA
    rwa [inv_inv] at this
  have ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G) := by
    intro ha'cd
    apply hacd
    rw [← hmapcd]
    exact ⟨a', ha'cd, by
      change g * (g⁻¹ * a * g) * g⁻¹ = a
      group⟩
  have ha'1 : a' ≠ 1 := fun h1 => ha'cd (h1 ▸ Subgroup.one_mem _)
  obtain ⟨-, -, -, -, hdK⟩ := basic_facts_of_conj h45 h hdL hA haA hacd
  have hdY : d ∈ Y := h.sec11K_le hdK
  obtain ⟨Y', hY', hKY'⟩ := exists_mem_thetaComponentsAt_sec11K_le h45 h48 h hdL hA ha'A ha'cd
  set Y'' := Y.map (MulAut.conj g).symm.toMonoidHom with hY''
  have hY''a : Y'' ∈ thetaComponentsAt 3 a' := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj g).symm h.mem_thetaComponentsAt_Y
    rwa [MulAut.conj_symm_apply] at h1
  have hdY'' : d ∈ Y'' := ⟨g * d * g⁻¹, Subgroup.zpowers_le.mpr hdY hgd, by
    change g⁻¹ * (g * d * g⁻¹) * g = d
    group⟩
  have hYeq : Y' = Y'' := by
    by_contra hne
    have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) :=
      Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe ha'A ha'1 Y' hY'
    have hdsec : d ∈ Late.sectionCentralizer A Y' (inSubgroup (aschbacherSolvableCore 3) Y') := by
      refine ⟨hdAL.1, fun y hy => ?_⟩
      have h1 := Sec10.commutator_mem_theta_of_ne hY''a hY' (Ne.symm hne) hdY'' hy
      have h2 : d * y * d⁻¹ * y⁻¹ ∈ Y' :=
        Y'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAY' hdAL.1) y).mp hy) (Y'.inv_mem hy)
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hY']
      exact ⟨h2, h1⟩
    exact hdc (mem_zpowers_of_mem_sectionCentralizer h45 h hdL hA ha'A ha'cd hKY'
      (Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)) hdsec)
  have hKY'' : sec11K L a' ≤ Y'' := hYeq ▸ hKY'
  have hφa : (MulAut.conj g) a' = a := by
    rw [MulAut.conj_apply, ha']
    group
  have hI : inSubgroup perfectResidual (Subgroup.centralizer {a} ⊓ Lg) =
      (sec11K L a').map (MulAut.conj g).toMonoidHom := by
    rw [sec11K, map_inSubgroup_perfectResidual, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      map_centralizer_singleton, hφa, inf_comm]
  have hIY : inSubgroup perfectResidual (Subgroup.centralizer {a} ⊓ Lg) ≤ Y := by
    rw [hI, ← map_map_symm (MulAut.conj g) Y]
    exact Subgroup.map_mono hKY''
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hθY : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) Y : Set G) :=
    hAY.trans (Sec6.normalizer_le_normalizer_theta Y)
  set S := sectionCentralizerSubgroup A Y (inSubgroup (aschbacherSolvableCore 3) Y) hAY hθY
    with hS
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have haS : a ∈ S := by
    refine ⟨haA, fun y hy => ?_⟩
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hYC hy), mul_inv_cancel_right,
      mul_inv_cancel]
    exact Subgroup.one_mem _
  have hθY'' : (inSubgroup (aschbacherSolvableCore 3) Y).map (MulAut.conj g).symm.toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) Y'' :=
    map_inSubgroup_aschbacherSolvableCore _ Y
  refine ⟨hdLg, hIY, ?_⟩
  ext z
  constructor
  · intro hz
    have hzS : z ∈ S := hz
    have hsup : A = Subgroup.closure ({c, d} : Set G) ⊔ Subgroup.zpowers a := by
      rw [hA, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
      congr 1
      ext y
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    have haN : Subgroup.zpowers a ≤
        Subgroup.normalizer (Subgroup.closure ({c, d} : Set G) : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y (hcdA hy) a haA)
    have hzA : z ∈ A := hz.1
    rw [hsup, sup_comm, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ haN] at hzA
    obtain ⟨y, hy, e, he, rfl⟩ := hzA
    have hyS : y ∈ S := Subgroup.zpowers_le.mpr haS hy
    have heS : e ∈ S := by
      have e1 : e = y⁻¹ * (y * e) := by group
      rw [e1]
      exact S.mul_mem (S.inv_mem hyS) hzS
    have he1 : e ∈ Subgroup.zpowers c :=
      mem_zpowers_of_mem_sectionCentralizer h45 h hdL hA haA hacd h.sec11K_le he heS
    have he2 : g⁻¹ * e * g ∈ Subgroup.zpowers c := by
      refine mem_zpowers_of_mem_sectionCentralizer h45 h hdL hA ha'A ha'cd hKY''
        (hconj e he) ⟨?_, fun y'' hy'' => ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgW) e).mp heS.1
        rwa [inv_inv] at this
      · obtain ⟨y₀, hy₀, rfl⟩ := hy''
        rw [← hθY'']
        refine ⟨_, heS.2 y₀ hy₀, ?_⟩
        change g⁻¹ * (e * y₀ * e⁻¹ * y₀⁻¹) * g =
          g⁻¹ * e * g * (g⁻¹ * y₀ * g) * (g⁻¹ * e * g)⁻¹ * (g⁻¹ * y₀ * g)⁻¹
        group
    have he1' : e = 1 := by
      by_contra hne
      apply hgH
      refine mem_normalizer_of_conj_mem_zpowers ?_
      have hord : orderOf e = 3 := orderOf_eq_prime (hexp e (hcdA he)) hne
      have hce : c ∈ Subgroup.zpowers e := by
        have heq : Subgroup.zpowers e = Subgroup.zpowers c :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he1)
            (by rw [Nat.card_zpowers, Nat.card_zpowers, hord,
              orderOf_eq_prime (hexp c hcA) h.ne_one])
        rw [heq]
        exact Subgroup.mem_zpowers c
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hce
      have e2 : g⁻¹ * c * g = (g⁻¹ * e * g) ^ k := by
        have e3 := conj_zpow (a := g⁻¹) (b := e) (i := k)
        rw [inv_inv] at e3
        rw [e3, hk]
      rw [e2]
      exact Subgroup.zpow_mem _ he2 k
    rw [he1']
    simpa using hy
  · intro hz
    exact Subgroup.zpowers_le.mpr haS hz

end CFSG.RankThree.PartTwo.Sec11
