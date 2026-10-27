module

public import CFSG.Quasithin.EmptyFaithful.S143UD
public import CFSG.Quasithin.EmptyFaithful.S143UC
public import CFSG.Quasithin.EmptyFaithful.S143UA
public import CFSG.Quasithin.EmptyFaithful.S143TA
public import CFSG.Quasithin.EmptyFaithful.S143UB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143


@[expose] def IsZ4StarSL23 (P : Type*) [Group P] : Prop :=
  Nat.card P = 48 ∧ ∃ A B : Subgroup P, IsCommutingGeneration A B ∧ Nat.card A = 4 ∧ IsCyclic A ∧
    Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

theorem sl3_central_sq : ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
    (∀ N : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), M * N = N * M) → M * M = 1 := by decide

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem card_sup_zpowers_of_sl23 {u₀ : G} {S : Subgroup G} (h4 : orderOf u₀ = 4)
    (hS : Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hcomm : S ≤ Subgroup.centralizer ({u₀} : Set G)) (hz : u₀ * u₀ ∈ S) :
    Nat.card ↥(Subgroup.zpowers u₀ ⊔ S) = 48 := by
  obtain ⟨e⟩ := hS
  have hA : Subgroup.zpowers u₀ ≤ Subgroup.centralizer (S : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcomm hs)
  have hprod := card_sup_mul_card_inf_of_le_centralizer hA
  have hSc : Nat.card ↥S = 24 := by
    rw [Nat.card_congr e.toEquiv]
    exact SL23.card_sl3
  have hu4 : u₀ ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one u₀
  have hsq1 : u₀ * u₀ ≠ 1 := fun h2 => by
    have : orderOf u₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [h4] at this; omega
  have hu₀S : u₀ ∉ S := by
    intro hu
    have hc : ∀ t : ↥S, (⟨u₀, hu⟩ : ↥S) * t = t * ⟨u₀, hu⟩ := fun t =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hcomm t.2)).symm
    have := sl3_central_sq (e ⟨u₀, hu⟩) (fun N => by
      have := congrArg e (hc (e.symm N))
      simpa using this)
    apply hsq1
    have h5 : (⟨u₀, hu⟩ : ↥S) * ⟨u₀, hu⟩ = 1 := e.injective (by rw [map_mul, map_one]; exact this)
    exact congrArg Subtype.val h5
  have hz' : u₀ * u₀ ∈ Subgroup.zpowers u₀ ⊓ S :=
    ⟨Subgroup.mul_mem _ (Subgroup.mem_zpowers u₀) (Subgroup.mem_zpowers u₀), hz⟩
  have hdvd : Nat.card ↥(Subgroup.zpowers u₀ ⊓ S) ∣ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers u₀ ⊓ S ≤ Subgroup.zpowers u₀)
    rwa [Nat.card_zpowers, h4] at this
  have hne1 : Nat.card ↥(Subgroup.zpowers u₀ ⊓ S) ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    have := hz'
    rw [h1, Subgroup.mem_bot] at this
    exact hsq1 this
  have hne4 : Nat.card ↥(Subgroup.zpowers u₀ ⊓ S) ≠ 4 := by
    intro h4'
    have heq : Subgroup.zpowers u₀ ⊓ S = Subgroup.zpowers u₀ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4', Nat.card_zpowers, h4])
    apply hu₀S
    have : u₀ ∈ Subgroup.zpowers u₀ ⊓ S := by rw [heq]; exact Subgroup.mem_zpowers u₀
    exact this.2
  have hle : Nat.card ↥(Subgroup.zpowers u₀ ⊓ S) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card ↥(Subgroup.zpowers u₀ ⊓ S) := Nat.card_pos
  have h3 : Nat.card ↥(Subgroup.zpowers u₀ ⊓ S) ≠ 3 := by
    intro h3'
    rw [h3'] at hdvd
    omega
  have h2 : Nat.card ↥(Subgroup.zpowers u₀ ⊓ S) = 2 := by omega
  rw [h2, Nat.card_zpowers, h4, hSc] at hprod
  omega

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}
  (c : Counter T M g) (c18 : Concl14318 T M g A t)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c c18 hD hd4 hxL hx3 in
theorem isZ4StarSL23_centralizer_oTwoUpper (hΓ : Subgroup.centralizer (A : Set G) = A) :
    IsZ4StarSL23 ↥(oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) := by
  classical
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hz1 : d * d ≠ 1 := (dd_facts hd4).2
  have hu₀U := u0Of_mem_U c c18 hD hd4 hxL hx3 hΓ
  have hu₀z := u0Of_sq c hD hd4 hxL hx3
  have hNd := oTwoUpper_le_centralizer_d c hD hd4
  have hCeq : oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({wOfX d x} : Set G) =
      oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({u0Of d x} : Set G) := by
    ext n
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hn, hnw⟩
      refine ⟨hn, ?_⟩
      have hnd : n * d = d * n := Subgroup.mem_centralizer_singleton_iff.mp (hNd hn)
      rw [wOfX_eq_mul_u0Of] at hnw
      have : d * (n * u0Of d x) = d * (u0Of d x * n) := by
        calc d * (n * u0Of d x) = (d * n) * u0Of d x := by group
          _ = (n * d) * u0Of d x := by rw [hnd]
          _ = n * (d * u0Of d x) := by group
          _ = (d * u0Of d x) * n := hnw
          _ = d * (u0Of d x * n) := by group
      exact mul_left_cancel this
    · rintro ⟨hn, hnu⟩
      refine ⟨hn, ?_⟩
      have hnd : n * d = d * n := Subgroup.mem_centralizer_singleton_iff.mp (hNd hn)
      rw [wOfX_eq_mul_u0Of]
      calc n * (d * u0Of d x) = (n * d) * u0Of d x := by group
        _ = (d * n) * u0Of d x := by rw [hnd]
        _ = d * (n * u0Of d x) := by group
        _ = d * (u0Of d x * n) := by rw [hnu]
        _ = (d * u0Of d x) * n := by group
  rw [hCeq]
  set u₀ := u0Of d x with hu₀def
  obtain ⟨hcard, ω, hωC, hω3⟩ := c.card_centralizer_oTwoUpper hzZ hz1 hu₀U hu₀z
  set C := oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({u₀} : Set G) with hC
  have hNH : oTwoUpper (mcOf T) ≤ mcOf T := oTwoUpper_le _
  have hωN : ω ∈ oTwoUpper (mcOf T) := hωC.1
  have hωH : ω ∈ mcOf T := hNH hωN
  have hωcomm : ω * u₀ = u₀ * ω := Subgroup.mem_centralizer_singleton_iff.mp hωC.2
  have hωωω : ω * ω * ω = 1 := by
    rw [← pow_three']; rw [← hω3]; exact pow_orderOf_eq_one ω
  have hωUn : ω ∈ Subgroup.normalizer (uOfL22 T M : Set G) := c.hHU hωH
  have hu₀nc : u₀ ∉ centerOf (uOfL22 T M) := by
    intro h
    rw [c.centerOf_uOfL22_eq] at h
    have := sq_eq_one_of_mem_omegaOneCenter T h
    rw [pow_two, hu₀z] at this
    exact hz1 this
  let α : MulAut ↥(uOfL22 T M) := (uOfL22 T M).normalizerMonoidHom ⟨ω, hωUn⟩
  have hα : ∀ p : ↥(uOfL22 T M), ((α p : ↥(uOfL22 T M)) : G) = ω * (p : G) * ω⁻¹ := fun p => rfl
  have hα3 : ∀ p, α (α (α p)) = p := fun p => Subtype.ext (by
    rw [hα, hα, hα]
    calc ω * (ω * (ω * (p : G) * ω⁻¹) * ω⁻¹) * ω⁻¹ = (ω * ω * ω) * (p : G) * (ω * ω * ω)⁻¹ := by
          group
      _ = p := by rw [hωωω]; group)
  have hαfix : α ⟨u₀, hu₀U⟩ = ⟨u₀, hu₀U⟩ := Subtype.ext (by
    rw [hα]
    show ω * u₀ * ω⁻¹ = u₀
    rw [hωcomm]; group)
  have hαne : ∃ p, α p ≠ p := by
    by_contra hcon
    push Not at hcon
    have hcent : ∀ u ∈ uOfL22 T M, ω * u * ω⁻¹ = u := fun u hu => congrArg Subtype.val (hcon ⟨u, hu⟩)
    have hk := c.actK_eq_one_of_centralizes hωH hcent
    have hωQ : ω ∈ qOf T := c.mem_qOf_of_actK_eq_one hk
    have hωU : ω ∈ uOfL22 T M := inf_qOf_le_uOfL22 c ⟨hωN, hωQ⟩
    have hωZ : ω ∈ centerOf (uOfL22 T M) := by
      refine ⟨hωU, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have := hcent u hu
      have h2 := congrArg (· * ω) this
      simpa [mul_assoc] using h2.symm
    rw [c.centerOf_uOfL22_eq] at hωZ
    have h2 := sq_eq_one_of_mem_omegaOneCenter T hωZ
    have h2' : ω * ω = 1 := by rw [← pow_two]; exact h2
    have h3 : ω = 1 := by
      calc ω = (ω * ω * ω) * (ω * ω)⁻¹ := by group
        _ = 1 := by rw [hωωω, h2']; group
    rw [h3, orderOf_one] at hω3
    omega
  obtain ⟨d₀⟩ := Q8SqData.nonempty_of_isQ8Sq c.c15.q8sq
  have hsqP : (⟨u₀, hu₀U⟩ : ↥(uOfL22 T M)) * ⟨u₀, hu₀U⟩ ≠ 1 := fun h =>
    hz1 (hu₀z ▸ congrArg Subtype.val h)
  have hncP : (⟨u₀, hu₀U⟩ : ↥(uOfL22 T M)) ∉ Subgroup.center ↥(uOfL22 T M) := fun h =>
    hu₀nc (mem_centerOf_iff_mem_center.mpr ⟨hu₀U, h⟩)
  have hord4 : orderOf u₀ = 4 := by
    refine orderOf_eq_four_of_sq (by rw [hu₀z]; exact hz1) ?_
    rw [hu₀z]
    exact (dd_facts hd4).1
  have key : ∀ d' : Q8SqData ↥(uOfL22 T M), (⟨u₀, hu₀U⟩ : ↥(uOfL22 T M)) ∈ d'.A →
      IsZ4StarSL23 ↥C := by
    intro d' hu₀A
    have hBα : ∀ b ∈ d'.B, α b ∈ d'.B := d'.map_B_le hu₀A hncP hsqP α hαfix
    have hmoved : ∃ b ∈ d'.B, α b ≠ b := by
      by_contra hcon
      push Not at hcon
      obtain ⟨p, hp⟩ := hαne
      exact hp (d'.fix_of_fix_B hu₀A hncP hsqP α hα3 hαfix hcon p)
    set B' : Subgroup G := d'.B.map (uOfL22 T M).subtype with hB'
    have hB'U : B' ≤ uOfL22 T M := by
      rintro _ ⟨b₀, _, rfl⟩
      exact b₀.2
    have hB'N : B' ≤ oTwoUpper (mcOf T) := hB'U.trans (uOfL22_le_oTwoUpper c)
    have hB'Q8 : Nonempty (↥B' ≃* QuaternionGroup 2) :=
      ⟨(Subgroup.equivMapOfInjective d'.B (uOfL22 T M).subtype
        (uOfL22 T M).subtype_injective).symm.trans d'.eB⟩
    have hB'comm : ∀ b ∈ B', b * u₀ = u₀ * b := by
      rintro _ ⟨b₀, hb₀, rfl⟩
      exact congrArg Subtype.val (d'.mul_comm_u0 hu₀A hb₀)
    have hB'ω : ∀ b ∈ B', ω * b * ω⁻¹ ∈ B' := by
      rintro _ ⟨b₀, hb₀, rfl⟩
      exact ⟨α b₀, hBα b₀ hb₀, rfl⟩
    have hB'nt : ∃ b ∈ B', ω * b * ω⁻¹ ≠ b := by
      obtain ⟨b₀, hb₀, hne⟩ := hmoved
      exact ⟨(b₀ : G), ⟨b₀, hb₀, rfl⟩, fun h => hne (Subtype.ext h)⟩
    have hS := SL23.nonempty_mulEquiv_sl23 hB'Q8 hω3 hB'ω hB'nt
    set S := B' ⊔ Subgroup.zpowers ω with hSdef
    have hSc : S ≤ Subgroup.centralizer ({u₀} : Set G) := by
      refine sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hB'comm b hb)) ?_
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hωcomm)
    have hSN : S ≤ oTwoUpper (mcOf T) := sup_le hB'N (Subgroup.zpowers_le.mpr hωN)
    have hz : u₀ * u₀ ∈ S := Subgroup.mem_sup_left ⟨_, d'.sq_mem_B hu₀A, rfl⟩
    have h48 := card_sup_zpowers_of_sl23 hord4 hS hSc hz
    have hAC : Subgroup.zpowers u₀ ≤ C :=
      Subgroup.zpowers_le.mpr ⟨uOfL22_le_oTwoUpper c hu₀U,
        Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hSC : S ≤ C := fun s hs => ⟨hSN hs, hSc hs⟩
    have hsupC : Subgroup.zpowers u₀ ⊔ S = C :=
      Subgroup.eq_of_le_of_card_ge (sup_le hAC hSC) (by rw [h48, hcard])
    refine ⟨hcard, (Subgroup.zpowers u₀).subgroupOf C, S.subgroupOf C, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      apply Subtype.ext
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp ha)
      have hsS := Subgroup.mem_subgroupOf.mp hs
      have hcm : (s : G) * u₀ = u₀ * (s : G) := Subgroup.mem_centralizer_singleton_iff.mp (hSc hsS)
      show (s : G) * (a : G) = (a : G) * (s : G)
      rw [← hk]
      exact (Commute.zpow_right (show Commute (s : G) u₀ from hcm) k).eq
    · rw [← Subgroup.subgroupOf_sup hAC hSC, hsupC, Subgroup.subgroupOf_self]
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, Nat.card_zpowers, hord4]
    · exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hAC)).mpr (Subgroup.isCyclic_zpowers u₀)
    · obtain ⟨e⟩ := hS
      exact ⟨(Subgroup.subgroupOfEquivOfLe hSC).trans e⟩
  rcases d₀.mem_A_or_mem_B hsqP with hA | hB
  · exact key d₀ hA
  · exact key d₀.swap' hB

end Main


end S143

end CFSG.Quasithin
