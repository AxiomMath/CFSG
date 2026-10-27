module

public import CFSG.Quasithin.H13.U3S1347O
public import CFSG.Quasithin.H13.U3S1347Y
public import CFSG.Quasithin.H13.U3S1347F

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem card_le_card_inf_centralizer_sq {U : Subgroup G}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a * a = 1) {t : G}
    (htU : t ∈ normalizer (U : Set G)) (ht2 : t * t ∈ centralizer (U : Set G)) :
    Nat.card U ≤ Nat.card ↥(U ⊓ centralizer ({t} : Set G)) ^ 2 := by
  have hconj : ∀ u ∈ U, t * u * t⁻¹ ∈ U := fun u hu => (mem_normalizer_iff.1 htU u).1 hu
  have hφU : ∀ u : ↥U, (u : G)⁻¹ * (t * u * t⁻¹) ∈ U := fun u =>
    mul_mem (inv_mem u.2) (hconj u u.2)
  let φ : ↥U →* ↥U :=
    { toFun := fun u => ⟨(u : G)⁻¹ * (t * u * t⁻¹), hφU u⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by
        show ((u : G) * v)⁻¹ * (t * (u * v) * t⁻¹) =
          (u : G)⁻¹ * (t * u * t⁻¹) * ((v : G)⁻¹ * (t * v * t⁻¹))
        calc ((u : G) * v)⁻¹ * (t * (u * v) * t⁻¹)
            = (v : G)⁻¹ * ((u : G)⁻¹ * (t * u * t⁻¹)) * (t * v * t⁻¹) := by group
          _ = (u : G)⁻¹ * (t * u * t⁻¹) * (v : G)⁻¹ * (t * v * t⁻¹) := by
            rw [hUc _ (inv_mem v.2) _ (hφU u)]
          _ = _ := by group) }
  have hφ : ∀ u : ↥U, ((φ u : ↥U) : G) = (u : G)⁻¹ * (t * u * t⁻¹) := fun _ => rfl
  have hker : φ.ker.map U.subtype ≤ U ⊓ centralizer ({t} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : (u : G)⁻¹ * (t * u * t⁻¹) = 1 := by
      rw [← hφ]
      exact congrArg Subtype.val hu
    have h2 : t * u * t⁻¹ = u := (inv_mul_eq_one.1 h1).symm
    refine mem_inf.2 ⟨u.2, mem_centralizer_singleton_iff.2 ?_⟩
    calc (u : G) * t = (t * u * t⁻¹) * t := by rw [h2]
      _ = t * u := by group
  have hran : φ.range.map U.subtype ≤ U ⊓ centralizer ({t} : Set G) := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨(φ u).2, mem_centralizer_singleton_iff.2 ?_⟩
    show (u : G)⁻¹ * (t * u * t⁻¹) * t = t * ((u : G)⁻¹ * (t * u * t⁻¹))
    have hx2 := hU2 _ (hφU u)
    have htt : (u : G) * (t * t) = (t * t) * u := (mem_centralizer_iff.1 ht2) u u.2
    calc (u : G)⁻¹ * (t * u * t⁻¹) * t = ((u : G)⁻¹ * (t * u * t⁻¹))⁻¹ * t := by
          rw [inv_eq_of_mul_eq_one_right hx2]
      _ = t * (u : G)⁻¹ * t⁻¹ * (u * (t * t)) * t⁻¹ := by group
      _ = t * (u : G)⁻¹ * t⁻¹ * ((t * t) * u) * t⁻¹ := by rw [htt]
      _ = t * ((u : G)⁻¹ * (t * u * t⁻¹)) := by group
  have h1 : Nat.card ↥U = Nat.card φ.ker * Nat.card φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  have h2 : Nat.card φ.ker ≤ Nat.card ↥(U ⊓ centralizer ({t} : Set G)) := by
    rw [← card_map_of_injective U.subtype_injective]
    exact card_le_of_le hker
  have h3 : Nat.card φ.range ≤ Nat.card ↥(U ⊓ centralizer ({t} : Set G)) := by
    rw [← card_map_of_injective U.subtype_injective]
    exact card_le_of_le hran
  rw [h1, sq]
  exact Nat.mul_le_mul h2 h3

theorem card_inf_centralizer_le_sq {U A B : Subgroup G}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a * a = 1) (hAB : A ≤ B)
    (h2 : A.relIndex B = 2) (hBU : B ≤ normalizer (U : Set G)) :
    Nat.card ↥(U ⊓ centralizer (A : Set G)) ≤ Nat.card ↥(U ⊓ centralizer (B : Set G)) ^ 2 := by
  have hidx : (A.subgroupOf B).index = 2 := h2
  have hlt : A < B := lt_of_le_of_ne hAB (by
    rintro rfl
    rw [relIndex_self] at h2
    omega)
  obtain ⟨t, htB, htA⟩ := IsConcreteLE.exists_of_lt hlt
  have hcos : ∀ b ∈ B, b ∉ A → t⁻¹ * b ∈ A := by
    intro b hb hbA
    have h1 := (mul_mem_iff_of_index_two hidx (a := ⟨t⁻¹, inv_mem htB⟩) (b := ⟨b, hb⟩)).2
      (iff_of_false (fun h => htA (by simpa using inv_mem (mem_subgroupOf.1 h)))
        (fun h => hbA (mem_subgroupOf.1 h)))
    exact mem_subgroupOf.1 h1
  have ht2 : t * t ∈ A := mem_subgroupOf.1 (mul_self_mem_of_index_two hidx ⟨t, htB⟩)
  have hnA : ∀ g ∈ B, ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun g hg a ha =>
    mem_subgroupOf.1 ((normal_of_index_eq_two hidx).conj_mem ⟨a, hAB ha⟩
      (mem_subgroupOf.2 ha) ⟨g, hg⟩)
  have htN : t ∈ normalizer (A : Set G) := by
    refine mem_normalizer_iff.2 fun a => ⟨fun ha => hnA t htB a ha, fun ha => ?_⟩
    have := hnA t⁻¹ (inv_mem htB) _ ha
    simpa [mul_assoc] using this
  have htU : t ∈ normalizer ((U ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_of (hBU htB) (mem_normalizer_centralizer_of_mem htN)
  have ht2' : t * t ∈ centralizer ((U ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun u hu => ((mem_centralizer_iff.1 (mem_inf.1 hu).2) _ ht2).symm
  have h1 := card_le_card_inf_centralizer_sq (U := U ⊓ centralizer (A : Set G))
    (fun a ha b hb => hUc a (mem_inf.1 ha).1 b (mem_inf.1 hb).1)
    (fun a ha => hU2 a (mem_inf.1 ha).1) htU ht2'
  have hle : (U ⊓ centralizer (A : Set G)) ⊓ centralizer ({t} : Set G) ≤
      U ⊓ centralizer (B : Set G) := by
    intro x hx
    obtain ⟨⟨hxU, hxA⟩, hxt⟩ := hx
    refine mem_inf.2 ⟨hxU, mem_centralizer_iff.2 fun b hb => ?_⟩
    by_cases hbA : b ∈ A
    · exact (mem_centralizer_iff.1 hxA) b hbA
    · have h3 := (mem_centralizer_iff.1 hxA) _ (hcos b hb hbA)
      have h4 : x * t = t * x := mem_centralizer_singleton_iff.1 hxt
      calc b * x = t * ((t⁻¹ * b) * x) := by group
        _ = t * (x * (t⁻¹ * b)) := by rw [h3]
        _ = (t * x) * t⁻¹ * b := by group
        _ = (x * t) * t⁻¹ * b := by rw [h4]
        _ = x * b := by group
  exact h1.trans (Nat.pow_le_pow_left (card_le_of_le hle) 2)

omit [Finite G] in
theorem map_pCoreOf_subgroupOf {I X : Subgroup G} (hXI : X ≤ I) :
    (pCoreOf 2 (X.subgroupOf I)).map I.subtype = pCoreOf 2 X := by
  have h := map_pCore_mulEquiv 2 (Subgroup.subgroupOfEquivOfLe hXI)
  unfold pCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl

theorem s1347_pCoreOf_ne (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) (hc₁ : Nat.card ↥(cZ T H₁) = 2)
    (hsolv : Group.IsSolvable ↥(H₁ ⊔ H₂))
    (hcomm : ¬ ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    pCoreOf 2 H₁ ≠ pCoreOf 2 H₂ := by
  intro heq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hred := s1347_reduced S hH₀
  have hP : H₁ ⊔ H₂ ≤ normalizer (v0Of T H₁ H₂ : Set G) := hred.2.1
  have hVc : ∀ a ∈ v0Of T H₁ H₂, ∀ b ∈ v0Of T H₁ H₂, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ a ∈ v0Of T H₁ H₂, a * a = 1 := fun a ha => by
    rw [← sq]
    exact hred.2.2.1.2 a ha
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have hO₁T := pCoreOf_two_le_of_isSylowTwoOf hsyl₁
  have h2₁ := relIndex_pCoreOf_T h.s3₁ h.inH₁.1 h3₁ hO₁T
  have hQ₀ : pCoreOf 2 H₁ ≤ pCoreOf 2 (H₁ ⊔ H₂) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 H₁).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 H₁) (by rw [heq]; exact le_normalizer_pCoreOf 2 H₂))
      (pCoreOf_isPGroup 2 H₁)
  have hQ₀' : pCoreOf 2 (H₁ ⊔ H₂) ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_two_le_of_isSylowTwoOf hsyl₀).trans h.inH₁.1)
      (le_sup_left.trans (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂))) (pCoreOf_isPGroup 2 (H₁ ⊔ H₂))
  have hTC : T ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 H₁ :=
    (s1347_T_inf_centralizer S h hH₀).trans (le_antisymm hQ₀' hQ₀)
  have hQC : pCoreOf 2 H₁ ≤ centralizer (v0Of T H₁ H₂ : Set G) := hTC.ge.trans inf_le_right
  have hlt : pCoreOf 2 H₁ < T := lt_of_le_of_ne hO₁T (by
    intro he
    rw [he, relIndex_self] at h2₁
    omega)
  obtain ⟨t, htT, htQ⟩ := IsConcreteLE.exists_of_lt hlt
  have hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4 := by rw [h.index₁, hc₁]
  have hVT : v0Of T H₁ H₂ ≤ T := s1347_V0_le_T S hH₀
  have hCZ : v0Of T H₁ H₂ ⊓ centralizer (T : Set G) ≤ quasithinOmegaOneCenter T :=
    fun x hx => subset_closure ⟨⟨hVT (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩,
      hred.2.2.1.2 x (mem_inf.1 hx).1⟩
  have hV16 : Nat.card ↥(v0Of T H₁ H₂) ≤ 16 := by
    have h1 := card_inf_centralizer_le_sq hVc hV2 hO₁T h2₁ (hH₀.1.trans hP)
    rw [inf_eq_left.2 (le_centralizer_iff.1 hQC)] at h1
    have h2 := card_le_of_le hCZ
    rw [hZ4] at h2
    calc Nat.card ↥(v0Of T H₁ H₂) ≤ _ := h1
      _ ≤ 4 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 16 := by norm_num
  have hmemX : ∀ g : ↥(H₁ ⊔ H₂), Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP g ∈
      autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) := fun g => (Setup.mem_autOn_self_iff hP).2 ⟨g, rfl⟩
  have hXs : Group.IsSolvable ↥(autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂)) := by
    rw [← Setup.range_rho hP]
    exact Group.isSolvable_of_surjective
      (Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP).rangeRestrict_surjective
  have hX2 : ∀ P : Subgroup ↥(autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂)), IsPGroup 2 ↥P →
      Nat.card ↥P ≤ 2 := by
    intro P hP2
    have hS := Setup.isSylowTwoOf_autOn hsyl₀ hP
    have hS2 : Nat.card ↥(autOn T (v0Of T H₁ H₂)) = 2 := by
      rw [card_autOn_eq_relIndex (hH₀.1.trans hP), hTC]
      exact h2₁
    have hXc : Nat.card ↥(autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂)) =
        (autOn T (v0Of T H₁ H₂)).relIndex (autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂)) * 2 := by
      have h1 := relIndex_mul_card (autOn T (v0Of T H₁ H₂)) (autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂))
      rw [inf_eq_left.2 hS.1, hS2] at h1
      exact h1.symm
    have hodd : ¬ 2 ∣ (autOn T (v0Of T H₁ H₂)).relIndex (autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂)) :=
      hS.2.2
    obtain ⟨a, ha⟩ := hP2.exists_card_eq
    have hdvd : 2 ^ a ∣
        (autOn T (v0Of T H₁ H₂)).relIndex (autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂)) * 2 := by
      rw [← ha, ← hXc]
      exact card_subgroup_dvd_card P
    have ha1 : a ≤ 1 := by
      by_contra hc
      have h4 : 2 * 2 ∣
          (autOn T (v0Of T H₁ H₂)).relIndex (autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂)) * 2 :=
        (pow_dvd_pow 2 (by omega : 2 ≤ a)).trans hdvd
      exact hodd (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h4)
    rw [ha]
    calc 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) ha1
      _ = 2 := by norm_num
  have h3dvd : 3 ∣ Nat.card ↥H₁ := by
    have := relIndex_mul_card T H₁
    rw [h3₁] at this
    exact Dvd.intro _ this
  obtain ⟨⟨x, hxH₁⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := ↥H₁) 3 h3dvd
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one (⟨x, hxH₁⟩ : ↥H₁)
    rw [hxo] at this
    simpa using congrArg Subtype.val this
  have hx1 : x ≠ 1 := by
    intro hx
    have : (⟨x, hxH₁⟩ : ↥H₁) = 1 := Subtype.ext hx
    rw [this, orderOf_one] at hxo
    omega
  have hxH₀ : x ∈ H₁ ⊔ H₂ := (le_sup_left : H₁ ≤ H₁ ⊔ H₂) hxH₁
  have htH₀ : t ∈ H₁ ⊔ H₂ := hH₀.1 htT
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⟨x, hxH₀⟩ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⟨t, htH₀⟩ := ⟨_, rfl⟩
  have hκ3 : κ ^ 3 = 1 := by
    rw [hκ, ← map_pow]
    have : (⟨x, hxH₀⟩ : ↥(H₁ ⊔ H₂)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hκ1 : κ ≠ 1 := by
    intro h1
    rw [hκ, Setup.rho_eq_one_iff] at h1
    exact hx1 (s1347_eq_one_of_threePow S h hH₀ ⟨hxH₀, h1⟩ (k := 1) (by rwa [pow_one]))
  have htk : τ * κ * τ⁻¹ = κ⁻¹ := by
    have hT3 := (s1347_triple S h).subgroupOf
    have hsI : (⟨t, htH₀⟩ : ↥(H₁ ⊔ H₂)) ∈
        H₁.subgroupOf (H₁ ⊔ H₂) ⊓ H₂.subgroupOf (H₁ ⊔ H₂) :=
      ⟨mem_subgroupOf.2 (h.inH₁.1 htT), mem_subgroupOf.2 (h.inH₂.1 htT)⟩
    have hsQ : (⟨t, htH₀⟩ : ↥(H₁ ⊔ H₂)) ∉ pCoreOf 2 (H₁.subgroupOf (H₁ ⊔ H₂)) := by
      intro hm
      apply htQ
      rw [← map_pCoreOf_subgroupOf (le_sup_left : H₁ ≤ H₁ ⊔ H₂)]
      exact ⟨_, hm, rfl⟩
    have hm := inv_mod_pCoreOf hT3 (x := ⟨x, hxH₀⟩) (mem_subgroupOf.2 hxH₁)
      (Subtype.ext (by simpa using hx3)) hsI hsQ
    have hm' : t * x * t⁻¹ * x ∈ centralizer (v0Of T H₁ H₂ : Set G) := by
      apply hQC
      rw [← map_pCoreOf_subgroupOf (le_sup_left : H₁ ≤ H₁ ⊔ H₂)]
      exact ⟨_, hm, rfl⟩
    have h1 : Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP
        (⟨t, htH₀⟩ * ⟨x, hxH₀⟩ * ⟨t, htH₀⟩⁻¹ * ⟨x, hxH₀⟩) = 1 :=
      (Setup.rho_eq_one_iff hP _).2 hm'
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    rw [hτ, hκ]
    exact eq_inv_of_mul_eq_one_left h1
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_two hc₁
  have huV : u ∈ v0Of T H₁ H₂ := s1347_Z_le_V0 (mem_inf.1 hu).1
  have hku : κ ⟨u, huV⟩ = ⟨u, huV⟩ := by
    apply Subtype.ext
    rw [hκ, Setup.rho_apply_coe]
    show x * u * x⁻¹ = u
    rw [mem_centralizer_iff.1 (mem_inf.1 hu).2 x hxH₁, mul_inv_cancel_right]
  have : IsMulCommutative ↥(v0Of T H₁ H₂) := hred.2.2.1.1
  have hκX : κ ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) := by
    rw [hκ]
    exact hmemX _
  have hτX : τ ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) := by
    rw [hτ]
    exact hmemX _
  obtain ⟨M, -, hMc, hodd⟩ := exists_abelian_of_small (W := ↥(v0Of T H₁ H₂))
    (fun w => Subtype.ext (hred.2.2.1.2 w w.2)) hV16 hXs hX2 hτX hκX hκ3 hκ1 htk
    (u := ⟨u, huV⟩) (fun h1 => hu1 (congrArg Subtype.val h1)) hku
  have hKM : ∀ {Hi : Subgroup G}, Hi ≤ H₁ ⊔ H₂ →
      oTwoRes Hi ≤ Setup.rhoPreimage (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP M := by
    intro Hi hHi
    rw [oTwoRes, closure_le]
    rintro y ⟨hyH, m, hm, hym⟩
    have h1 : orderOf (⟨y, hHi hyH⟩ : ↥(H₁ ⊔ H₂)) ∣ m :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hym))
    have h2 : (⟨y, hHi hyH⟩ : ↥(H₁ ⊔ H₂)).1 ∈
        Setup.rhoPreimage (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP M :=
      Setup.mem_rhoPreimage.2 (hodd _ (hmemX _) (Odd.of_dvd_nat hm
        ((orderOf_map_dvd _ _).trans h1)))
    exact h2
  apply hcomm
  rw [commutator_le]
  intro a ha b hb
  have haH : a ∈ H₁ ⊔ H₂ := Setup.rhoPreimage_le hP M (hKM le_sup_left ha)
  have hbH : b ∈ H₁ ⊔ H₂ := Setup.rhoPreimage_le hP M (hKM le_sup_right hb)
  have haM := (Setup.mem_rhoPreimage (p := ⟨a, haH⟩)).1 (hKM le_sup_left ha)
  have hbM := (Setup.mem_rhoPreimage (p := ⟨b, hbH⟩)).1 (hKM le_sup_right hb)
  have h1 : Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP ⁅(⟨a, haH⟩ : ↥(H₁ ⊔ H₂)), ⟨b, hbH⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hMc _ haM _ hbM
  exact (Setup.rho_eq_one_iff hP _).1 h1

end CFSG.Quasithin.H13.U3
