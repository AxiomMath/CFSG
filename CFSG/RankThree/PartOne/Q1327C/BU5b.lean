module

public import CFSG.RankThree.PartOne.Q1327C.BU5Ab
public import CFSG.RankThree.PartOne.Q1327C.BU5Ctr
public import CFSG.RankThree.PartOne.Q1327C.BU5Refl

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFU
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G] [Finite G]

theorem false_of_u5_five {X A₀ F : Subgroup G} (h : Q1327.T123Base 5 X A₀ F)
    (hirr : ∀ B : Subgroup G, B ≤ F → torusInvariant F X B → B = ⊥ ∨ B = F)
    (hrefl : ∃ t : MulAut ↥F, t ∈ torusImage F X ∧ IsAutReflection 5 F t)
    (hm : ∃ f : ℕ, 1 ≤ f ∧ 25 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 5 2 f) : False := by
  classical
  obtain ⟨f, hf1, h25, hcl⟩ := hm
  have h5 : 5 ∣ 2 ^ f + 1 := dvd_trans (by norm_num) h25
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hcl
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf1
  let π : ↥(SU5 f K) →* StatedProj (SU5 f K) := QuotientGroup.mk' (ZSU5 f K)
  let πY : ↥(SU5 f K) →* (↥X ⧸ Subgroup.center ↥X) := e.symm.toMonoidHom.comp π
  have hπY : Function.Surjective πY := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerY : πY.ker = ZSU5 f K := by
    ext x
    rw [MonoidHom.mem_ker]
    show e.symm (π x) = 1 ↔ x ∈ ZSU5 f K
    rw [map_eq_one_iff e.symm e.symm.injective]
    exact QuotientGroup.eq_one_iff (N := ZSU5 f K) x
  have hZMcard : Nat.card (ZSU5 f K) = 5 := by
    have hcard := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
      (by norm_num : 1 ≤ 5)).2.2
    rw [show ZSU5 f K = (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ f) K) from rfl,
      hcard]
    exact Nat.gcd_eq_left h5
  have hZMc : ∀ z ∈ ZSU5 f K, ∀ g : ↥(SU5 f K), g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.1
      (CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center (F := K) 5 (2 ^ f) hz) g
  have hZM5 : ∀ z ∈ ZSU5 f K, z ^ 5 = 1 := fun z hz => by
    have := Subgroup.orderOf_dvd_natCard (ZSU5 f K) hz
    rw [hZMcard] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hkerz : ∀ z : ↥(SU5 f K), πY z = 1 → z ∈ ZSU5 f K := fun z hz => by
    rw [← hkerY]
    exact hz
  have hkerc : ∀ z : ↥(SU5 f K), πY z = 1 → ∀ g : ↥(SU5 f K), g * z = z * g :=
    fun z hz g => hZMc z (hkerz z hz) g
  have hker5 : ∀ z : ↥(SU5 f K), πY z = 1 → z ^ 5 = 1 := fun z hz => hZM5 z (hkerz z hz)
  have hel := barF_elem h
  have hE5 := barF_exp h
  have hEc : ∀ x ∈ bar X F, ∀ y ∈ bar X F, x * y = y * x := fun x hx y hy => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := bar X F)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this
  by_cases hab : ∀ x ∈ (bar X F).comap πY, ∀ y ∈ (bar X F).comap πY, x * y = y * x
  ·
    obtain ⟨V, hV5, hVc, hFV, hVcard⟩ := exists_big_elementary hU h25 πY hkerY hZMcard hE5 hab
    have hFV' : bar X F ≤ V := by
      have : ((bar X F).comap πY).map πY = bar X F :=
        Subgroup.map_comap_eq_self_of_surjective hπY _
      rwa [this] at hFV
    have hVel : IsElementaryAbelian 5 V := by
      refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
      · apply Subtype.ext
        exact hVc _ a.2 _ b.2
      · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
        apply Subtype.ext
        exact hV5 _ x.2
    have hA₀ : bar X A₀ ≤ bar X F := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, h.A₀_le_F hx, rfl⟩
    have hC : V ≤ Subgroup.centralizer ((bar X A₀ : Subgroup (↥X ⧸ Subgroup.center ↥X)) :
        Set (↥X ⧸ Subgroup.center ↥X)) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haP : a ∈ V := hFV' (hA₀ ha)
      have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := V)).comm ⟨a, haP⟩ ⟨y, hy⟩)
      simpa using this
    have hEq : V = bar X F :=
      bar_maximal h.prime h.center_pPrime h.F_le h.F_elem h.A₀_le_F h.F_max hVel hFV' hC
    have h1 := barF_card h
    rw [← hEq] at h1
    omega
  ·
    push Not at hab
    obtain ⟨t, htT, htR⟩ := hrefl
    obtain ⟨ℓF, hℓne, hℓinv, hℓgen⟩ := reflection_data htR
    obtain ⟨n, hnX, hn⟩ := htT
    have hnX' : (n : G) ∈ X := hnX
    have hnN : (n : G) ∈ Subgroup.normalizer (F : Set G) := n.2
    set nY : ↥X ⧸ Subgroup.center ↥X := proj X ⟨(n : G), hnX'⟩ with hnYdef
    have hnYN := mem_normalizer_bar hnX' hnN
    have hnYE : ∀ e ∈ bar X F, nY * e * nY⁻¹ ∈ bar X F := fun e he =>
      ((Subgroup.mem_normalizer_iff.1 hnYN) e).1 he
    let ψF : ↥F ≃* ↥(bar X F) := barF_equiv h
    have hψF : ∀ f : ↥F, ((ψF f : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) =
        proj X ⟨(f : G), h.F_le f.2⟩ := fun f => rfl
    have hact : ∀ f : ↥F, ((ψF (t f) : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) =
        nY * ((ψF f : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) * nY⁻¹ := by
      intro f
      rw [hψF, hψF, hnYdef, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [← hn]
      rfl
    have hℓYE : ((ψF ℓF : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) ∈ bar X F := (ψF ℓF).2
    have hℓYinv : nY * ((ψF ℓF : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) * nY⁻¹ =
        ((ψF ℓF : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X)⁻¹ := by
      rw [← hact, hℓinv, map_inv]
      rfl
    have hLY : ∀ y ∈ bar X F, ∃ k : ℤ, nY * y * nY⁻¹ * y⁻¹ =
        ((ψF ℓF : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) ^ k := by
      intro y hy
      obtain ⟨f, hf⟩ := ψF.surjective ⟨y, hy⟩
      obtain ⟨k, hk⟩ := hℓgen f
      refine ⟨k, ?_⟩
      have h1 : ((ψF f : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) = y :=
        congrArg Subtype.val hf
      rw [← h1, ← hact]
      have h2 := congrArg (fun z : ↥F => ((ψF z : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X)) hk
      simpa [map_mul, map_inv, map_zpow] using h2
    obtain ⟨ℓM, hℓM, hℓMc⟩ := exists_central_lift πY hπY hkerc hker5 hEc hnYE hℓYE hℓYinv hLY
    have hℓYR : ((ψF ℓF : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) ∈
        liftCenter πY (bar X F) := ⟨hℓYE, ℓM, hℓM, hℓMc⟩
    let Rb : Subgroup ↥(bar X F) := (liftCenter πY (bar X F)).subgroupOf (bar X F)
    let B : Subgroup G := (Rb.comap ψF.toMonoidHom).map F.subtype
    have hBF : B ≤ F := Subgroup.map_subtype_le _
    have hBmem : ∀ f : ↥F, (f : G) ∈ B ↔
        ((ψF f : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) ∈ liftCenter πY (bar X F) := by
      intro f
      constructor
      · rintro ⟨b', hb', hb'f⟩
        have : b' = f := Subtype.ext hb'f
        subst this
        exact hb'
      · intro hf
        exact ⟨f, hf, rfl⟩
    have hinv : torusInvariant F X B := by
      intro w hw b hb
      obtain ⟨hwX, hwN⟩ := Subgroup.mem_inf.1 hw
      have hwN' : w ∈ Subgroup.normalizer (F : Set G) := hwN
      have hbF : b ∈ F := hBF hb
      have hwbF : w * b * w⁻¹ ∈ F := ((Subgroup.mem_normalizer_iff.1 hwN') b).1 hbF
      have hb' : ((ψF ⟨b, hbF⟩ : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) ∈
          liftCenter πY (bar X F) := (hBmem ⟨b, hbF⟩).1 hb
      have hnW := mem_normalizer_bar hwX hwN'
      have hact' : ((ψF ⟨w * b * w⁻¹, hwbF⟩ : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) =
          proj X ⟨w, hwX⟩ * ((ψF ⟨b, hbF⟩ : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) *
            (proj X ⟨w, hwX⟩)⁻¹ := by
        rw [hψF, hψF, ← map_inv, ← map_mul, ← map_mul]
        congr 1
      have := liftCenter_conj πY hπY hnW hb'
      rw [← hact'] at this
      exact (hBmem ⟨w * b * w⁻¹, hwbF⟩).2 this
    rcases hirr B hBF hinv with hB | hB
    ·
      have hmem : (ℓF : G) ∈ B := (hBmem ℓF).2 hℓYR
      rw [hB, Subgroup.mem_bot] at hmem
      exact hℓne (Subtype.ext hmem)
    ·
      have hle : bar X F ≤ liftCenter πY (bar X F) := by
        intro y hy
        obtain ⟨f, hf⟩ := ψF.surjective ⟨y, hy⟩
        have h1 : ((ψF f : ↥(bar X F)) : ↥X ⧸ Subgroup.center ↥X) = y := congrArg Subtype.val hf
        rw [← h1]
        exact (hBmem f).1 (by rw [hB]; exact f.2)
      obtain ⟨x, hx, y, hy, hxy⟩ := hab
      exact hxy (comm_of_le_liftCenter πY hkerc hle hx hy)

end CFSG.RankThree.PartOne.Q1327C
