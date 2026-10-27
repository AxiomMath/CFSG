module

public import CFSG.Quasithin.Vol2.E2NineTIBase
public import CFSG.Quasithin.Vol2.E2SevenKG3
public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftAux
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace E2

theorem isSimpleGroup_of_isBenderOf' {X : Type} [Group X] {n : ℕ} (h : IsBenderOf n X) :
    IsSimpleGroup X := by
  obtain ⟨-, hY | hY | hY⟩ := h
  · exact isSimpleGroup_of_psl_or_sz (Or.inl hY)
  · exact isSimpleGroup_of_psl_or_sz (Or.inr hY)
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 n hY).2

theorem nonabelian_of_isBenderOf {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsBenderOf n X) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨k, hB⟩ := exists_fusionBenderBorel_of_isBenderOf h
  by_contra hab
  simp only [ne_eq, not_exists, not_not] at hab
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨hSE, -⟩ := hB P
  apply hSE.1
  rw [eq_top_iff]
  intro g _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have : g * x * g⁻¹ = x := by rw [hab g x]; group
  rw [this]

variable {Y : Type} [Group Y] [Finite Y]

theorem le_normalizer_or_eq_of_isBenderOf
    {K S X : Subgroup Y} {n : ℕ} (hBen : IsBenderOf n ↥K)
    (hS : IsSylowTwoOf S K) (hSX : S ≤ X) (hXK : X ≤ K) :
    X ≤ Subgroup.normalizer (S : Set Y) ∨ X = K := by
  obtain ⟨k, hB⟩ := exists_fusionBenderBorel_of_isBenderOf hBen
  have hs := isSimpleGroup_of_isBenderOf' hBen
  by_cases hXN : X ≤ Subgroup.normalizer (S : Set Y)
  · exact Or.inl hXN
  right
  set P := toSylow2 hS
  have hPc : (P : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  have hPX : (P : Subgroup ↥K) ≤ X.subgroupOf K := by
    rw [hPc]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hSX (Subgroup.mem_subgroupOf.mp hx))
  have hXN' : ¬ X.subgroupOf K ≤ Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K) := by
    intro hle
    apply hXN
    intro y hy
    have hyK := hXK hy
    have h1 := hle (Subgroup.mem_subgroupOf.mpr hy : (⟨y, hyK⟩ : ↥K) ∈ X.subgroupOf K)
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro z
    constructor
    · intro hz
      have h2 := (h1 ⟨z, hS.1 hz⟩).mp (by rw [hPc]; exact Subgroup.mem_subgroupOf.mpr hz)
      rw [hPc] at h2
      exact Subgroup.mem_subgroupOf.mp h2
    · intro hz
      have hzK : z ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem hyK) (hS.1 hz)) hyK
        simpa [mul_assoc] using this
      have h2 := (h1 ⟨z, hzK⟩).mpr (by rw [hPc]; exact Subgroup.mem_subgroupOf.mpr hz)
      rw [hPc] at h2
      exact Subgroup.mem_subgroupOf.mp h2
  have htop := eq_top_of_sylow_le hBen.1 hB hs P hPX hXN'
  refine le_antisymm hXK fun x hx => ?_
  have : (⟨x, hx⟩ : ↥K) ∈ X.subgroupOf K := by rw [htop]; trivial
  exact Subgroup.mem_subgroupOf.mp this

theorem exists_conj_center_of_isBenderOf_top {X : Type} [Group X] [Finite X] {n : ℕ}
    (hBen : IsBenderOf n X) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) :
    Nat.card ↥(S ⊓ Subgroup.centralizer (S : Set X)) = 2 ^ n ∧
      ∀ z₁ ∈ S ⊓ Subgroup.centralizer (S : Set X), ∀ z₂ ∈ S ⊓ Subgroup.centralizer (S : Set X),
        z₁ ≠ 1 → z₂ ≠ 1 → ∃ m ∈ Subgroup.normalizer (S : Set X), m⁻¹ * z₁ * m = z₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hB⟩ := exists_fusionBenderBorel_of_isBenderOf hBen
  have hB' : fusionBenderBorel ↥(⊤ : Subgroup X) (2 ^ n) j :=
    hB.map_mulEquiv Subgroup.topEquiv.symm
  obtain ⟨hcard, hsq⟩ := card_inf_centralizer_of_fusionBenderBorel hB' hS
  refine ⟨hcard, fun z₁ hz₁ z₂ hz₂ h₁ h₂ => ?_⟩
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have hSE := (hB (hS.2.1.toSylow hidx)).1
  exact CFSG.ComponentClassification.AschbacherToolkit.Bender.normalizer_transitive_center hSE hsq
    hz₁ hz₂ h₁ h₂

omit [Finite Y] in
theorem isSylowTwoOf_subgroupOf_top_of {K S : Subgroup Y} (hS : IsSylowTwoOf S K) :
    IsSylowTwoOf (S.subgroupOf K) (⊤ : Subgroup ↥K) := by
  refine ⟨le_top, ?_, ?_⟩
  · have e : ↥(S.subgroupOf K) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hS.1
    exact hS.2.1.of_injective e.toMonoidHom e.injective
  · have h := hS.2.2
    have e : ((S.subgroupOf K).subgroupOf (⊤ : Subgroup ↥K)).index = (S.subgroupOf K).index :=
      Subgroup.index_comap_of_surjective (S.subgroupOf K) (f := (⊤ : Subgroup ↥K).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    rw [e]
    exact h

theorem exists_conj_center_of_isBenderOf {K S : Subgroup Y} {n : ℕ} (hBen : IsBenderOf n ↥K)
    (hS : IsSylowTwoOf S K) :
    Nat.card ↥(S ⊓ Subgroup.centralizer (S : Set Y)) = 2 ^ n ∧
      ∀ z₁ ∈ S ⊓ Subgroup.centralizer (S : Set Y), ∀ z₂ ∈ S ⊓ Subgroup.centralizer (S : Set Y),
        z₁ ≠ 1 → z₂ ≠ 1 → ∃ m ∈ K ⊓ Subgroup.normalizer (S : Set Y), m⁻¹ * z₁ * m = z₂ := by
  set S' := S.subgroupOf K with hS'def
  obtain ⟨hcard, htr⟩ := exists_conj_center_of_isBenderOf_top hBen
    (isSylowTwoOf_subgroupOf_top_of hS)
  have hto : ∀ (z : Y) (hz : z ∈ S ⊓ Subgroup.centralizer (S : Set Y)),
      (⟨z, hS.1 hz.1⟩ : ↥K) ∈ S' ⊓ Subgroup.centralizer (S' : Set ↥K) := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hz.1,
      Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hz.2) w (Subgroup.mem_subgroupOf.mp hw))
  have hfrom : ∀ z : ↥K, z ∈ S' ⊓ Subgroup.centralizer (S' : Set ↥K) →
      (z : Y) ∈ S ⊓ Subgroup.centralizer (S : Set Y) := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hz).1,
      Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have h1 := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2) ⟨w, hS.1 hw⟩
      (Subgroup.mem_subgroupOf.mpr hw)
    exact congrArg Subtype.val h1
  refine ⟨?_, fun z₁ hz₁ z₂ hz₂ h₁ h₂ => ?_⟩
  · rw [← hcard]
    refine Nat.card_congr (Equiv.ofBijective (fun z : ↥(S ⊓ Subgroup.centralizer (S : Set Y)) =>
      (⟨⟨z, hS.1 z.2.1⟩, hto z z.2⟩ : ↥(S' ⊓ Subgroup.centralizer (S' : Set ↥K))))
      ⟨fun a b hab => ?_, fun w => ?_⟩)
    · have := congrArg (fun x : ↥(S' ⊓ Subgroup.centralizer (S' : Set ↥K)) => ((x : ↥K) : Y)) hab
      exact Subtype.ext this
    · exact ⟨⟨(w : ↥K), hfrom w w.2⟩, rfl⟩
  · obtain ⟨m, hm, hmz⟩ := htr _ (hto z₁ hz₁) _ (hto z₂ hz₂)
      (fun h => h₁ (congrArg Subtype.val h)) (fun h => h₂ (congrArg Subtype.val h))
    have hmN : (m : Y) ∈ Subgroup.normalizer (S : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 := (Subgroup.mem_normalizer_iff.mp hm ⟨x, hS.1 hx⟩).mp
          (Subgroup.mem_subgroupOf.mpr hx)
        exact Subgroup.mem_subgroupOf.mp h1
      · intro hx
        have hxK : x ∈ K := by
          have := K.mul_mem (K.mul_mem (K.inv_mem m.2) (hS.1 hx)) m.2
          simpa [mul_assoc] using this
        have h1 := (Subgroup.mem_normalizer_iff.mp hm ⟨x, hxK⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hx)
        exact Subgroup.mem_subgroupOf.mp h1
    exact ⟨m, Subgroup.mem_inf.mpr ⟨m.2, hmN⟩, congrArg Subtype.val hmz⟩

section Star

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

omit [Finite G] in
theorem mem_of_starMap_mem_star {x : G} (hxH : x ∈ H)
    (hx : E2P.starMap M H ⟨x, hxH⟩ ∈ star M H M) : x ∈ M := by
  obtain ⟨⟨m, hmH⟩, hm, hmx⟩ := hx
  have h1 : (m : G)⁻¹ * x ∈ kerIn M H := by
    have := QuotientGroup.eq.1 hmx
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have := M.mul_mem (Subgroup.mem_subgroupOf.mp hm) (kerIn_le h1)
  simpa using this

omit [Finite G] in
theorem commutator_mem_kerIn_of_commute {x y : G} (hx : x ∈ H) (hy : y ∈ H)
    (hc : E2P.starMap M H ⟨x, hx⟩ * E2P.starMap M H ⟨y, hy⟩ =
      E2P.starMap M H ⟨y, hy⟩ * E2P.starMap M H ⟨x, hx⟩) : ⁅x, y⁆ ∈ kerIn M H := by
  have hmem : ⁅x, y⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  have h1 : E2P.starMap M H ⟨⁅x, y⁆, hmem⟩ = 1 := by
    have e : (⟨⁅x, y⁆, hmem⟩ : ↥H) = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩)⁻¹ * (⟨y, hy⟩)⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have h2 : (⟨⁅x, y⁆, hmem⟩ : ↥H) ∈ (E2P.starMap M H).ker := h1
  rw [E2P.ker_starMap, Subgroup.mem_subgroupOf] at h2
  exact h2

omit [Finite G] in
theorem isElemAbelian_star {X : Subgroup G} (hX : IsElemAbelian 2 X) :
    IsElemAbelian 2 (star M H X) := by
  refine ⟨⟨⟨fun ⟨a, x, hx, hxa⟩ ⟨b, y, hy, hyb⟩ => Subtype.ext ?_⟩⟩, ?_⟩
  · subst hxa hyb
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    have hc := hX.1.is_comm.comm (⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩ : X)
      ⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩
    exact Subtype.ext (congrArg (fun z : X => (z : G)) hc)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hX.2 _ (Subgroup.mem_subgroupOf.1 hx))
    rw [this, map_one]

theorem star_pCoreOf_le (hmp : MinParabolic H T M) :
    star M H (pCoreOf 2 M) ≤ pCoreOf 2 (star M H M) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (star_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 M)) ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_injective
      (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 M).trans
        hmp.maximal.1.le)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe _).injective |>.map _)
  rintro _ ⟨⟨m, hmH⟩, hm, rfl⟩
  exact starMap_mem_normalizer hmH
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (Subgroup.mem_subgroupOf.1 hm))

omit [Finite G] in
theorem a1bConjSub_eq (g : G) (X : Subgroup G) : A1b.conjSub g X = conjSub g X := by
  ext x
  rw [A1b.mem_conjSub_iff, mem_conjSub]

end Star

section Main

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem le_nParam_of_bender_ti
    (hKG1 : KGBenderInner) (h : Hyp28 H T M V) (hTI : IsTISetIn V M)
    (hsq : SQTKGroup ↥(⊤ : Subgroup (StarQuot M H))) {L : Subgroup (StarQuot M H)}
    (hLn : L.Normal) (hLT : L ⊔ star M H T = ⊤) {n : ℕ} (hBen : IsBenderOf n ↥L) :
    (n : ℕ∞) ≤ E1.nParam H := by
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have hY28 := h.star hsq
  have hmpY := E2P.minParabolic_star h.minParabolic
  have hJY : kerIn (star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
  have hs := isSimpleGroup_of_isBenderOf' hBen
  have hnab := nonabelian_of_isBenderOf hBen
  have hLN : (⊤ : Subgroup (StarQuot M H)) ≤ Subgroup.normalizer (L : Set (StarQuot M H)) :=
    fun x _ => Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hLn.conj_mem y hy x,
      fun hy => by simpa [mul_assoc] using hLn.conj_mem _ hy x⁻¹⟩
  have hcent := centralizer_eq_bot_of_simple hmpY hJY hLn hs hnab hLT
  set Ts := star M H T with hTs
  set Ms := star M H M with hMs
  set U := Ts ⊓ L with hU
  have hS : IsSylowTwoOf U L := A4.isSylowTwoOf_inf_normal hmpY.isSylow le_top hLN
  obtain ⟨hZcard, htrans⟩ := exists_conj_center_of_isBenderOf hBen hS
  set Z := U ⊓ Subgroup.centralizer (U : Set (StarQuot M H)) with hZ
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hBen.1
  have hTU : Ts ≤ Subgroup.normalizer (U : Set (StarQuot M H)) := fun t ht =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer ht) (hLN (Subgroup.mem_top t))
  have hNU : (⊤ : Subgroup (StarQuot M H)) ⊓ Subgroup.normalizer (U : Set (StarQuot M H)) ≤ Ms := by
    refine hmpY.le_of_lt (le_inf le_top hTU) (lt_of_le_of_ne inf_le_left fun heq => ?_)
    have hUN : (⊤ : Subgroup (StarQuot M H)) ≤ Subgroup.normalizer (U : Set (StarQuot M H)) :=
      heq ▸ inf_le_right
    have hUO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top hUN hS.2.1
    have hU1 : U = ⊥ := le_bot_iff.mp (hUO.trans (hmpY.pCoreOf_le_kerIn.trans hJY.le))
    have h1 : Nat.card ↥Z = 1 := by rw [hZ, hU1, bot_inf_eq, Subgroup.card_bot]
    omega
  have hMK : Ms ⊓ L = L ⊓ Subgroup.normalizer (U : Set (StarQuot M H)) := by
    refine le_antisymm ?_ (le_inf ((le_inf le_top inf_le_right).trans hNU) inf_le_left)
    rcases le_normalizer_or_eq_of_isBenderOf hBen hS
        (le_inf (inf_le_left.trans hmpY.le) inf_le_right) inf_le_right with h1 | h1
    · exact le_inf inf_le_right h1
    · exfalso
      have hLM : L ≤ Ms := h1 ▸ inf_le_left
      have htop : (⊤ : Subgroup (StarQuot M H)) ≤ Ms := by
        rw [← hLT]
        exact sup_le hLM hmpY.le
      exact hmpY.maximal.1.not_ge htop
  obtain ⟨hO2K, hcentral⟩ := hKG1 (StarQuot M H) ⊤ Ts Ms L n hmpY hJY le_top hLN
    (by rw [top_inf_eq]; exact hcent) hLT hBen hMK
  set E := tiClosure M V with hEdef
  have hEel := h.isElemAbelian_tiClosure hTI
  have hEO := h.tiClosure_le_pCoreOf
  have hET : E ≤ T := hEO.trans h.pCoreOf_M_le_T
  have hEH : E ≤ H := hET.trans hTH
  have hVE : V ≤ E := le_tiClosure
  have hEJ : ¬ E ≤ kerIn M H := fun hle => h.not_le_kerIn (hVE.trans hle)
  have hEsel := isElemAbelian_star (M := M) (H := H) hEel
  have hEsU : star M H E ≤ U :=
    le_inf (star_mono hET) (((star_mono hEO).trans (star_pCoreOf_le h.minParabolic)).trans hO2K)
  have hEsZ : star M H E ≤ Z := fun x hx => ⟨hEsU hx, hcentral x (hEsU hx) (hEsel.2 x hx)⟩
  have hEsN : Ms ≤ Subgroup.normalizer (star M H E : Set (StarQuot M H)) := by
    rintro _ ⟨⟨m, hmH⟩, hm, rfl⟩
    exact starMap_mem_normalizer hmH (le_normalizer_tiClosure (Subgroup.mem_subgroupOf.1 hm))
  have hEs1 : star M H E ≠ ⊥ := fun hb => hY28.ne_bot (le_bot_iff.mp (hb ▸ star_mono hVE))
  have hEsZeq : star M H E = Z := by
    refine le_antisymm hEsZ fun z hz => ?_
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEs1
    have he1' : e ≠ 1 := fun h' => he1 (Subtype.ext h')
    by_cases hz1 : z = 1
    · rw [hz1]; exact (star M H E).one_mem
    obtain ⟨m, hm, hmz⟩ := htrans e (hEsZ he) z hz he1' hz1
    have hmM : m ∈ Ms := (hMK.symm ▸ hm : m ∈ Ms ⊓ L).1
    rw [← hmz]
    have := (Subgroup.mem_normalizer_iff.mp (hEsN (Ms.inv_mem hmM)) e).mp he
    simpa using this
  have hEscard : Nat.card ↥(star M H E) = 2 ^ n := by rw [hEsZeq]; exact hZcard
  refine le_nParam_of_forall_isE h.minParabolic hET hEel hEJ ?_
  intro i _ hin g hg hAT K' hE'
  by_contra hK'M
  obtain ⟨hK'H, hτ, -, hEE⟩ := hE'
  set A := A1b.conjSub g E with hAdef
  have hAeq : A = conjSub g E := a1bConjSub_eq g E
  have hAH : A ≤ H := hAT.trans hTH
  have hAel : IsElemAbelian 2 A := isElemAbelian_cjSub hEel
  have h1 : star M H A = conjSub (E2P.starMap M H ⟨g, hg⟩) (star M H E) := by
    rw [hAeq]
    exact star_conjSub hg
  have hAsU : star M H A ≤ U := by
    refine le_inf (star_mono hAT) ?_
    rw [h1]
    intro x hx
    rw [mem_conjSub] at hx
    have := hLn.conj_mem _ (hEsU hx).2 (E2P.starMap M H ⟨g, hg⟩)
    simpa [mul_assoc] using this
  have hAsel := isElemAbelian_star (M := M) (H := H) hAel
  have hAs : star M H A = Z := by
    have hle : star M H A ≤ Z := fun x hx => ⟨hAsU hx, hcentral x (hAsU hx) (hAsel.2 x hx)⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [h1, B6.card_conjSub, hEscard, hZcard]
  have hτK : ∀ (t : G) (ht : t ∈ T), E2P.starMap M H ⟨t, hTH ht⟩ ∈ U → t ∈ K' := by
    intro t ht htU
    refine (hτ (mem_tauOf_of_commutator_mem_kerIn h.minParabolic hAT ht fun a ha => ?_)).2
    have haZ : E2P.starMap M H ⟨a, hAH ha⟩ ∈ Z := hAs ▸ starMap_mem_star (hAH ha) ha
    exact commutator_mem_kerIn_of_commute (hTH ht) (hAH ha)
      ((Subgroup.mem_centralizer_iff.mp haZ.2) _ htU)
  have hUK' : U ≤ star M H K' := by
    intro u hu
    obtain ⟨⟨t, htH⟩, ht, rfl⟩ := hu.1
    exact starMap_mem_star htH (hτK t (Subgroup.mem_subgroupOf.mp ht) hu)
  have hK'Ms : ¬ star M H K' ≤ Ms := by
    intro hle
    apply hK'M
    intro k hk
    exact mem_of_starMap_mem_star (hK'H hk) (hle (starMap_mem_star (hK'H hk) hk))
  have hLK' : L ≤ star M H K' := by
    rcases le_normalizer_or_eq_of_isBenderOf hBen hS (le_inf hUK' hS.1) inf_le_right with
      h2 | h2
    · exfalso
      apply hK'Ms
      intro x hx
      refine hNU ⟨Subgroup.mem_top x, ?_⟩
      have hxD : cjSub x (star M H K' ⊓ L) = star M H K' ⊓ L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx) (hLN (Subgroup.mem_top x)))
      have hcj : cjSub x U ≤ star M H K' ⊓ L := by
        rw [← hxD]
        exact cjSub_mono (le_inf hUK' hS.1)
      have h3 : IsPGroup 2 ↥(cjSub x U ⊔ U) :=
        IsPGroup.to_sup_of_normal_right' (hS.2.1.map _) hS.2.1 (hcj.trans h2)
      have hxU : cjSub x U ≤ U := le_sup_left.trans
        ((A4.isSylowTwoOf_iff_maximal.mp hS).2.2 _
          (sup_le (hcj.trans inf_le_right) hS.1) h3 le_sup_right)
      apply mem_normalizer_of_cjSub_eq
      exact Subgroup.eq_of_le_of_card_ge hxU (by rw [card_cjSub])
    · exact h2 ▸ inf_le_left
  have hAK' : A ≤ K' := fun a ha => (hτ (mem_tauOf_of_commutator_mem_kerIn h.minParabolic hAT
    (hAT ha) fun a' ha' => by
      have := hAel.1
      have hc : a * a' = a' * a := setLike_mul_comm ha ha'
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
      exact (kerIn M H).one_mem)).2
  have hR := solvableRadical_map_le_kerIn hK'H hLK' hLn hs hnab hcent
  have hcardle := card_star_le_card_barRad hK'H hAK' hR
  rw [hAs, hZcard] at hcardle
  have hlt : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hin
  rcases hEE with ⟨hE1, -⟩ | ⟨-, h3⟩
  ·
    have hsol := E1.RootLift.isSolvable_of_eOne hE1
    have h4 : Group.IsSolvable ↥(K'.subgroupOf H) := Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hK'H).symm.toMonoidHom) (MulEquiv.surjective _)
    have h5 : Group.IsSolvable ↥(star M H K') := Group.isSolvable_of_surjective
      (f := (E2P.starMap M H).subgroupMap (K'.subgroupOf H))
      ((E2P.starMap M H).subgroupMap_surjective _)
    have hsolL : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hLK') (Subgroup.inclusion_injective _)
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolL a b)
  · omega

end Main

end E2

end CFSG.Quasithin
