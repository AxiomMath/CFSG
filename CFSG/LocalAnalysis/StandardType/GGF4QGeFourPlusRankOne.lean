module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusRankOneNative
import CFSG.LieType.BorelTits.LeviOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal Multiplicative Module
open CFSG.RankThree.Classical2 (orthDerived)

section Transport

variable {G : Type} [Group G] {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem ggRankOneIn_eq_map_native {Bs L : Subgroup G} {ψΩ : ↥(orthDerived Q) →* G}
    (hψinj : Function.Injective ψΩ) (hψrange : ψΩ.range = L) {ℓΩ : ↥Bs →* ↥(orthDerived Q)}
    (hcompat : ∀ (b : ↥Bs) (z : ↥(orthDerived Q)),
      (b : G)⁻¹ * ψΩ z * (b : G) = ψΩ (ℓΩ b * z * (ℓΩ b)⁻¹))
    {φ : MulAut ↥Bs} {a b : ↥(orthDerived Q)}
    (hgen : ∀ b' : ↥Bs, φ b' = b' → ∃ m n : ℕ, ℓΩ b' = a ^ m * b ^ n)
    (ha : ∃ ba : ↥Bs, φ ba = ba ∧ ℓΩ ba = a) (hb : ∃ bb : ↥Bs, φ bb = bb ∧ ℓΩ bb = b) :
    ggRankOneIn L Bs φ =
      (ggOTwoPrime (Subgroup.centralizer ({a, b} : Set ↥(orthDerived Q)))).map ψΩ := by
  classical
  set CΩ : Subgroup ↥(orthDerived Q) := Subgroup.centralizer ({a, b} : Set ↥(orthDerived Q))
    with hCΩ
  have hcomm : ∀ (b' : ↥Bs) (z : ↥(orthDerived Q)),
      (b' : G) * ψΩ z = ψΩ z * (b' : G) ↔ ℓΩ b' * z = z * ℓΩ b' := by
    intro b' z
    constructor
    · intro h
      have h1 := hcompat b' z
      have h2 : (b' : G)⁻¹ * ψΩ z * (b' : G) = ψΩ z := by
        rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h2] at h1
      have h3 := hψinj h1
      calc ℓΩ b' * z = ℓΩ b' * z * (ℓΩ b')⁻¹ * ℓΩ b' := by group
        _ = z * ℓΩ b' := by rw [← h3]
    · intro h
      have h1 := hcompat b' z
      have h2 : ℓΩ b' * z * (ℓΩ b')⁻¹ = z := by rw [h, mul_inv_cancel_right]
      rw [h2] at h1
      calc (b' : G) * ψΩ z = (b' : G) * ((b' : G)⁻¹ * ψΩ z * (b' : G)) := by rw [h1]
        _ = ψΩ z * (b' : G) := by group
  have heq : L ⊓ Subgroup.centralizer (ggHyperplane Bs φ : Set G) = CΩ.map ψΩ := by
    apply le_antisymm
    · rintro g ⟨hgL, hgC⟩
      rw [← hψrange] at hgL
      obtain ⟨z, rfl⟩ := hgL
      refine ⟨z, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
      intro w hw
      obtain ⟨bw, hbw, hbwz⟩ : ∃ bw : ↥Bs, φ bw = bw ∧ ℓΩ bw = w := by
        rcases hw with h | h
        · rw [h]
          exact ha
        · rw [Set.mem_singleton_iff.mp h]
          exact hb
      rw [← hbwz]
      have hmem : (bw : G) ∈ ggHyperplane Bs φ := (mem_ggHyperplane_iff' bw).mpr hbw
      exact (hcomm bw z).mp (Subgroup.mem_centralizer_iff.mp hgC _ hmem)
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨by rw [← hψrange]; exact ⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      obtain ⟨b', hb', rfl⟩ := hh
      have hfix : φ b' = b' := hb'
      obtain ⟨m, n, hmn⟩ := hgen b' hfix
      have hz' := Subgroup.mem_centralizer_iff.mp hz
      have hza : a * z = z * a := hz' a (by simp)
      have hzb : b * z = z * b := hz' b (by simp)
      have hc : Commute (ℓΩ b') z := by
        rw [hmn]
        exact ((Commute.pow_left hza m).mul_left (Commute.pow_left hzb n))
      exact (hcomm b' z).mpr hc.eq
  rw [ggRankOneIn, heq, ggOTwoPrime_map_of_injective ψΩ hψinj]

theorem map_subtype_ggOTwoPrime_centralizer (a b : ↥(orthDerived Q)) :
    (ggOTwoPrime (Subgroup.centralizer ({a, b} : Set ↥(orthDerived Q)))).map
        (orthDerived Q).subtype =
      ggOTwoPrime (orthDerived Q ⊓
        Subgroup.centralizer ({(a : V ≃ₗ[K] V), (b : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))) := by
  classical
  set CΩ : Subgroup ↥(orthDerived Q) := Subgroup.centralizer ({a, b} : Set ↥(orthDerived Q))
    with hCΩ
  have hmapC : CΩ.map (orthDerived Q).subtype = orthDerived Q ⊓
      Subgroup.centralizer ({(a : V ≃ₗ[K] V), (b : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    ext g
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' := Subgroup.mem_centralizer_iff.mp hz
      refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro w hw
      rcases hw with h | h
      · rw [h]
        exact congrArg Subtype.val (hz' a (by simp))
      · rw [Set.mem_singleton_iff.mp h]
        exact congrArg Subtype.val (hz' b (by simp))
    · rintro ⟨hgΩ, hgC⟩
      have hgC' := Subgroup.mem_centralizer_iff.mp hgC
      refine ⟨⟨g, hgΩ⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
      intro w hw
      rcases hw with h | h
      · rw [h]
        exact Subtype.ext (hgC' _ (by simp))
      · rw [Set.mem_singleton_iff.mp h]
        exact Subtype.ext (hgC' _ (by simp))
  rw [ggOTwoPrime_map_of_injective _ (orthDerived Q).subtype_injective, hmapC]

theorem ggRankOneIn_equiv_native {Bs L : Subgroup G} {ψΩ : ↥(orthDerived Q) →* G}
    (hψinj : Function.Injective ψΩ) (hψrange : ψΩ.range = L) {ℓΩ : ↥Bs →* ↥(orthDerived Q)}
    (hcompat : ∀ (b : ↥Bs) (z : ↥(orthDerived Q)),
      (b : G)⁻¹ * ψΩ z * (b : G) = ψΩ (ℓΩ b * z * (ℓΩ b)⁻¹))
    {φ : MulAut ↥Bs} {a b : ↥(orthDerived Q)}
    (hgen : ∀ b' : ↥Bs, φ b' = b' → ∃ m n : ℕ, ℓΩ b' = a ^ m * b ^ n)
    (ha : ∃ ba : ↥Bs, φ ba = ba ∧ ℓΩ ba = a) (hb : ∃ bb : ↥Bs, φ bb = bb ∧ ℓΩ bb = b) :
    Nonempty (↥(ggRankOneIn L Bs φ) ≃* ↥(ggOTwoPrime (orthDerived Q ⊓
      Subgroup.centralizer ({(a : V ≃ₗ[K] V), (b : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))))) := by
  rw [ggRankOneIn_eq_map_native hψinj hψrange hcompat hgen ha hb,
    ← map_subtype_ggOTwoPrime_centralizer]
  exact ⟨((ggOTwoPrime _).equivMapOfInjective ψΩ hψinj).symm.trans
    ((ggOTwoPrime _).equivMapOfInjective _ (orthDerived Q).subtype_injective)⟩

end Transport

section Main

set_option maxHeartbeats 2000000 in
theorem plusMember_native {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    (hp : p.Prime) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) {ψ : (ggU .POmegaMinus 4 f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K) (hrange : ψ.range = X)
    {ℓ : ↥Bs →* (ggU .POmegaMinus 4 f).K}
    (hℓ : ∀ (b : ↥Bs) (u : (ggU .POmegaMinus 4 f).K),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hkerℓ : ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G))
    (hZX : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p)
    (hrankℓ : p ^ 3 ≤ Nat.card ℓ.range) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (GaloisField 2 f) V)
      (_ : FiniteDimensional (GaloisField 2 f) V) (Q : QuadraticForm (GaloisField 2 f) V)
      (ψΩ : ↥(orthDerived Q) →* G) (τ : (Fin 3 → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
      (cv : ↥Bs → Fin 3 → ZMod p),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ Function.Injective ψΩ ∧ ψΩ.range = X ∧
      Nat.card ↥Bs = p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
      (∀ b b' : ↥Bs, cv (b * b') = cv b + cv b') ∧ (∀ v, ∃ b, cv b = v) ∧
      (∀ m : Fin 3, finrank (GaloisField 2 f) (CFSG.RankThree.PartOne.LIT.commSpace
        ((τ (Pi.mulSingle m (ofAdd 1)) : ↥(orthDerived Q)) : V ≃ₗ[GaloisField 2 f] V)) = 2) ∧
      (∀ φ ∈ ggAutomizer X Bs, ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ b, cv (φ b) = OmPlusFrame.spAct π ε (cv b)) ∧
      (∀ φ ∈ ggAutomizer X Bs, (∀ b, cv (φ b) = cv b) → φ = 1) ∧
      ∀ φ ∈ ggAutomizer X Bs, GGIsReflection p φ →
        ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) →
        (∀ b, cv (φ b) = OmPlusFrame.spAct π ε (cv b)) →
        CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs φ) ∧
        (π = 1 → Nat.card ↥(ggRankOneIn X Bs φ) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) ∧
          ∃ j, ε j = -1 ∧ (∀ i, i ≠ j → ε i = 1) ∧
            ∀ k l : Fin 3, k ≠ l → k ≠ j → l ≠ j →
              ggRankOneIn X Bs φ = (ggOTwoPrime (Subgroup.centralizer
                ({τ (Pi.mulSingle k (ofAdd 1)), τ (Pi.mulSingle l (ofAdd 1))} :
                  Set ↥(orthDerived Q)))).map ψΩ) ∧
        (π ≠ 1 → Nat.card ↥(ggRankOneIn X Bs φ) = 2 ^ f * ((2 ^ f) ^ 2 - 1) ∧
          ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ π i = i ∧ π j = k ∧ π k = j ∧
            ε j = ε k ∧ ε i = 1 ∧
            ∃ h : Polynomial (GaloisField 2 f), h ≠ Polynomial.X - 1 ∧
              h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors
                ((τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j))) :
                  ↥(orthDerived Q)) : V ≃ₗ[GaloisField 2 f] V).toLinearMap ∧
              ggRankOneIn X Bs φ = (ggOTwoPrime (Subgroup.centralizer
                ({τ (Pi.mulSingle i (ofAdd 1)),
                  τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j)))} :
                  Set ↥(orthDerived Q)))).map ψΩ ∧
              (ggOTwoPrime (Subgroup.centralizer
                ({τ (Pi.mulSingle i (ofAdd 1)),
                  τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j)))} :
                  Set ↥(orthDerived Q)))).map (orthDerived Q).subtype =
                CFSG.RankThree.PartOne.KCOrthogonal.specialBlock Q
                  ((τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j))) :
                    ↥(orthDerived Q)) : V ≃ₗ[GaloisField 2 f] V) h ∧
              CFSG.RankThree.PartOne.LIT.commSpace
                  ((τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j))) :
                    ↥(orthDerived Q)) : V ≃ₗ[GaloisField 2 f] V) =
                CFSG.RankThree.PartOne.LIT.commSpace
                    ((τ (Pi.mulSingle j (ofAdd 1)) : ↥(orthDerived Q)) :
                      V ≃ₗ[GaloisField 2 f] V) ⊔
                  CFSG.RankThree.PartOne.LIT.commSpace
                    ((τ (Pi.mulSingle k (ofAdd 1)) : ↥(orthDerived Q)) :
                      V ≃ₗ[GaloisField 2 f] V)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 1 :=
      (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hpq
    omega
  have hcommBs : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hpowBs : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hirr := minusCoeffs_irr 2 f
  let Q := Spin.quadMinus 4 (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let ψn : ↥(spinGroup Q) →* G := ψ
  let ℓn : ↥Bs →* ↥(spinGroup Q) := ℓ
  have hcenU : Subgroup.center ↥(spinGroup Q) = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (by decide : 4 ≤ 4) hirr
  have hψinj : Function.Injective ψn := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hcenU.le
  let ι := Spin.spinEquivCommutatorQuadMinus (n := 4) le_rfl hirr
    (CharTwo.two_eq_zero (R := GaloisField 2 f))
  let ψΩ : ↥(orthDerived Q) →* G := ψn.comp ι.symm.toMonoidHom
  let ℓΩ : ↥Bs →* ↥(orthDerived Q) := ι.toMonoidHom.comp ℓn
  have hψΩinj : Function.Injective ψΩ := hψinj.comp ι.symm.injective
  have hψΩrange : ψΩ.range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.symm.surjective,
      ← MonoidHom.range_eq_map]
    exact hrange
  have hcompat : ∀ (b : ↥Bs) (z : ↥(orthDerived Q)),
      (b : G)⁻¹ * ψΩ z * (b : G) = ψΩ (ℓΩ b * z * (ℓΩ b)⁻¹) := by
    intro b z
    have h1 : ι.symm (ℓΩ b * z * (ℓΩ b)⁻¹) = ℓn b * ι.symm z * (ℓn b)⁻¹ := by
      simp only [ℓΩ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
        MulEquiv.symm_apply_apply]
    show (b : G)⁻¹ * ψn (ι.symm z) * b = ψn (ι.symm (ℓΩ b * z * (ℓΩ b)⁻¹))
    rw [h1]
    exact hℓ b (ι.symm z)
  have hcenΩ : Subgroup.center ↥(orthDerived Q) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : ι.symm z ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply ι.injective
      rw [map_mul, map_mul, ι.apply_symm_apply]
      exact hz (ι g)
    rw [hcenU, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← ι.apply_symm_apply z, hz', map_one]
  have hEΩ : ℓΩ.range.map (orthDerived Q).subtype ≤ orthDerived Q := Subgroup.map_subtype_le _
  have hpowE : ∀ a ∈ ℓΩ.range.map (orthDerived Q).subtype, a ^ p = 1 := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    rw [← map_pow, ← map_pow, hpowBs b, map_one, map_one]
  have hcommE : ∀ a ∈ ℓΩ.range.map (orthDerived Q).subtype,
      ∀ b ∈ ℓΩ.range.map (orthDerived Q).subtype, a * b = b * a := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩ _ ⟨_, ⟨b', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcommBs b b']
  have hcardE : p ^ 3 ≤ Nat.card (ℓΩ.range.map (orthDerived Q).subtype) := by
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective]
    have hr : ℓΩ.range = ℓn.range.map ι.toMonoidHom := MonoidHom.range_comp _ _
    rw [hr, Subgroup.card_map_of_injective ι.injective]
    exact hrankℓ
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.RankThree.PartOne.S15K.polar_nondegenerate_quadMinus hirr
  have hdim8 : finrank (GaloisField 2 f) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) =
      8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
    CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega) hirr
  have hpqF : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hF]; exact hpq
  obtain ⟨τ, Fr, Db, _, _, _, cb, θ, hτF, hτinj, hτrange, hD2, hcp, hcfix, hctw, hθinj, hθrange,
    hθact, hU2, hcU, hnorm⟩ :=
    OmPlusFrame.exists_plusBlocks hQnd hdim8 hminus hp hp2 hpqF hEΩ hpowE hcommE hcardE
  have hmemτ : ∀ b : ↥Bs, (orthDerived Q).subtype.comp ℓΩ b ∈ τ.range := fun b => by
    rw [hτrange]
    exact ⟨ℓΩ b, ⟨b, rfl⟩, rfl⟩
  let c : ↥Bs →* (Fin 3 → Multiplicative (ZMod p)) :=
    (MonoidHom.ofInjective hτinj).symm.toMonoidHom.comp
      (((orthDerived Q).subtype.comp ℓΩ).codRestrict τ.range hmemτ)
  have hc : ∀ b, τ (c b) = (ℓΩ b).1 := fun b =>
    congrArg Subtype.val ((MonoidHom.ofInjective hτinj).apply_symm_apply
      (((orthDerived Q).subtype.comp ℓΩ).codRestrict τ.range hmemτ b))
  have hcker : ∀ b, c b = 1 ↔ ℓΩ b = 1 := by
    intro b
    constructor
    · intro h
      have := hc b
      rw [h, map_one] at this
      exact Subtype.ext this.symm
    · intro h
      apply hτinj
      rw [hc, h, map_one]
      rfl
  have hcsurj : ∀ f' : Fin 3 → Multiplicative (ZMod p), ∃ b, c b = f' := by
    intro f'
    have h1 : τ f' ∈ ℓΩ.range.map (orthDerived Q).subtype := hτrange ▸ ⟨f', rfl⟩
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h1
    exact ⟨b, hτinj ((hc b).trans hb)⟩
  have hA := fun {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer X Bs) =>
    plusFrame_spAct_of_mem_ggAutomizer hψΩinj hψΩrange hcenΩ hcompat hnorm hc hφ
  let cv : ↥Bs → Fin 3 → ZMod p := fun b i => toAdd (c b i)
  have hcv_act : ∀ {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → ZMod p} {φ : MulAut ↥Bs},
      (∀ b i, toAdd (c (φ b) (π i)) = ε i * toAdd (c b i)) →
        ∀ b, cv (φ b) = OmPlusFrame.spAct π ε (cv b) := by
    intro π ε φ hφ b
    funext k
    have h1 := hφ b (π.symm k)
    rw [Equiv.apply_symm_apply] at h1
    exact h1
  have hcvsurj : ∀ v : Fin 3 → ZMod p, ∃ b, cv b = v := by
    intro v
    obtain ⟨b, hb⟩ := hcsurj fun i => ofAdd (v i)
    exact ⟨b, funext fun i => by simp only [cv, hb, toAdd_ofAdd]⟩
  have hcv0 : ∀ b, cv b = 0 ↔ ℓΩ b = 1 := by
    intro b
    rw [← hcker]
    constructor
    · intro h
      funext i
      have := congrFun h i
      simpa [cv] using this
    · intro h
      funext i
      simp [cv, h]
  have hτΩ' : ∀ g, τ g ∈ orthDerived Q := fun g => hEΩ (hτrange ▸ ⟨g, rfl⟩)
  let τh : (Fin 3 → Multiplicative (ZMod p)) →* ↥(orthDerived Q) :=
    τ.codRestrict (orthDerived Q) hτΩ'
  have hper : ∀ φ ∈ ggAutomizer X Bs, GGIsReflection p φ →
      ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) →
      (∀ b, cv (φ b) = OmPlusFrame.spAct π ε (cv b)) →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs φ) ∧
        (π = 1 → Nat.card ↥(ggRankOneIn X Bs φ) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) ∧
          ∃ j, ε j = -1 ∧ (∀ i, i ≠ j → ε i = 1) ∧
            ∀ k l : Fin 3, k ≠ l → k ≠ j → l ≠ j →
              ggRankOneIn X Bs φ = (ggOTwoPrime (Subgroup.centralizer
                ({τh (Pi.mulSingle k (ofAdd 1)), τh (Pi.mulSingle l (ofAdd 1))} :
                  Set ↥(orthDerived Q)))).map ψΩ) ∧
        (π ≠ 1 → Nat.card ↥(ggRankOneIn X Bs φ) = 2 ^ f * ((2 ^ f) ^ 2 - 1) ∧
          ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ π i = i ∧ π j = k ∧ π k = j ∧
            ε j = ε k ∧ ε i = 1 ∧
            ∃ h : Polynomial (GaloisField 2 f), h ≠ Polynomial.X - 1 ∧
              h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors
                (τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j)))).toLinearMap ∧
              ggRankOneIn X Bs φ = (ggOTwoPrime (Subgroup.centralizer
                ({τh (Pi.mulSingle i (ofAdd 1)),
                  τh (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j)))} :
                  Set ↥(orthDerived Q)))).map ψΩ ∧
              (ggOTwoPrime (Subgroup.centralizer
                ({τh (Pi.mulSingle i (ofAdd 1)),
                  τh (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j)))} :
                  Set ↥(orthDerived Q)))).map (orthDerived Q).subtype =
                CFSG.RankThree.PartOne.KCOrthogonal.specialBlock Q
                  (τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j)))) h ∧
              CFSG.RankThree.PartOne.LIT.commSpace
                  (τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε j)))) =
                CFSG.RankThree.PartOne.LIT.commSpace (τ (Pi.mulSingle j (ofAdd 1))) ⊔
                  CFSG.RankThree.PartOne.LIT.commSpace (τ (Pi.mulSingle k (ofAdd 1)))) := by
    intro φ hφL hφ π ε hε hcvφ
    have hkφ := (hA hφL).2
    have hφ2 : φ * φ = 1 := by rw [← pow_two]; exact hφ.1
    have h2 : ∀ v, OmPlusFrame.spAct π ε (OmPlusFrame.spAct π ε v) = v := by
      intro v
      obtain ⟨b, rfl⟩ := hcvsurj v
      rw [← hcvφ, ← hcvφ, ← MulAut.mul_apply, hφ2, MulAut.one_apply]
    have hfixiff : ∀ b : ↥Bs, φ b = b ↔ OmPlusFrame.spAct π ε (cv b) = cv b := by
      intro b
      constructor
      · intro h
        rw [← hcvφ, h]
      · intro h
        have hcb : c (φ b) = c b := by
          funext i
          apply toAdd.injective
          have := congrFun ((hcvφ b).trans h) i
          simpa [cv] using this
        have hk : ℓΩ (φ b * b⁻¹) = 1 :=
          (hcker _).mp (by rw [map_mul, map_inv, hcb, mul_inv_cancel])
        obtain ⟨k, hkdef⟩ : ∃ k, k = φ b * b⁻¹ := ⟨_, rfl⟩
        rw [← hkdef] at hk
        have hφb : φ b = k * b := by rw [hkdef, inv_mul_cancel_right]
        have hφφ : φ (φ b) = b := by rw [← MulAut.mul_apply, hφ2, MulAut.one_apply]
        have h3 : φ (φ b) = k * k * b := by rw [hφb, map_mul, hkφ k hk, hφb, mul_assoc]
        rw [hφφ] at h3
        have hkk : k * k = 1 := by
          have h5 := congrArg (· * b⁻¹) h3
          simpa [mul_assoc] using h5.symm
        have hk1 : k = 1 := by
          have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
          have h6 := (pow_gcd_eq_one (a := k) (m := 2) (n := p)).mpr
            ⟨by rw [pow_two, hkk], hpowBs k⟩
          rwa [hcop.gcd_eq_one, pow_one] at h6
        rw [hφb, hk1, one_mul]
    let S' : Subgroup (Fin 3 → Multiplicative (ZMod p)) :=
      { carrier := {g | OmPlusFrame.spAct π ε (fun i => toAdd (g i)) = fun i => toAdd (g i)}
        mul_mem' := fun {g g'} hg hg' => by
          have hg1 : OmPlusFrame.spAct π ε (fun i => toAdd (g i)) = fun i => toAdd (g i) := hg
          have hg2 : OmPlusFrame.spAct π ε (fun i => toAdd (g' i)) = fun i => toAdd (g' i) := hg'
          show OmPlusFrame.spAct π ε (fun i => toAdd ((g * g') i)) = fun i => toAdd ((g * g') i)
          funext m
          have e1 := congrFun hg1 m
          have e2 := congrFun hg2 m
          simp only [OmPlusFrame.spAct] at e1 e2 ⊢
          simp only [Pi.mul_apply, toAdd_mul]
          rw [mul_add, e1, e2]
        one_mem' := by
          show OmPlusFrame.spAct π ε (fun i => toAdd ((1 : Fin 3 → Multiplicative (ZMod p)) i)) =
            fun i => toAdd ((1 : Fin 3 → Multiplicative (ZMod p)) i)
          funext m
          simp [OmPlusFrame.spAct]
        inv_mem' := fun {g} hg => by
          have hg1 : OmPlusFrame.spAct π ε (fun i => toAdd (g i)) = fun i => toAdd (g i) := hg
          show OmPlusFrame.spAct π ε (fun i => toAdd (g⁻¹ i)) = fun i => toAdd (g⁻¹ i)
          funext m
          have e1 := congrFun hg1 m
          simp only [OmPlusFrame.spAct] at e1 ⊢
          simp only [Pi.inv_apply, toAdd_inv]
          rw [mul_neg, e1] }
    have hmemS : ∀ b : ↥Bs, b ∈ S'.comap c ↔ φ b = b := fun b => by
      rw [hfixiff b]
      rfl
    have hcardH : Nat.card ↥(S'.comap c) = Nat.card {b : ↥Bs // φ b = b} :=
      Nat.card_congr (Equiv.subtypeEquivRight hmemS)
    have hidx : (S'.comap c).index = S'.index :=
      Subgroup.index_comap_of_surjective S' (fun f' => hcsurj f')
    have hH := Subgroup.card_mul_index (S'.comap c)
    have hS := Subgroup.card_mul_index S'
    have hrefl := hφ.2
    rw [← hcardH] at hrefl
    have hpos : 0 < Nat.card ↥(S'.comap c) := Nat.card_pos
    have hidxp : (S'.comap c).index = p := by
      have : Nat.card ↥(S'.comap c) * (S'.comap c).index = Nat.card ↥(S'.comap c) * p := by
        rw [hH, hrefl]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have hcardV : Nat.card (Fin 3 → Multiplicative (ZMod p)) = p ^ 3 := by
      rw [Nat.card_fun, Nat.card_fin,
        show Nat.card (Multiplicative (ZMod p)) = p from
          (Nat.card_congr Multiplicative.ofAdd.symm).trans (Nat.card_zmod p)]
    rw [← hidx, hidxp, hcardV] at hS
    have hcardS : Nat.card ↥S' = p ^ 2 := by
      have : Nat.card ↥S' * p = p ^ 2 * p := by rw [hS]; ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    have hcardFx : Nat.card {v : Fin 3 → ZMod p // OmPlusFrame.spAct π ε v = v} = p ^ 2 := by
      rw [← hcardS]
      exact Nat.card_congr
        { toFun := fun v => ⟨fun i => ofAdd (v.1 i), by
            show OmPlusFrame.spAct π ε (fun i => toAdd (ofAdd (v.1 i))) =
              fun i => toAdd (ofAdd (v.1 i))
            simpa using v.2⟩
          invFun := fun g => ⟨fun i => toAdd (g.1 i), g.2⟩
          left_inv := fun v => by
            apply Subtype.ext
            funext i
            simp
          right_inv := fun g => by
            apply Subtype.ext
            funext i
            simp }
    have hK1 := OmPlusFrame.eq_one_of_pow_eq_one_of_dvd_add_one hp hp2 hpqF
    have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hτmem : ∀ g, τ g ∈ ℓΩ.range.map (orthDerived Q).subtype := fun g => hτrange ▸ ⟨g, rfl⟩
    have hτΩ : ∀ g, τ g ∈ orthDerived Q := fun g => hEΩ (hτmem g)
    have hτpow : ∀ g, τ g ^ p = 1 := fun g => hpowE _ (hτmem g)
    have hτcomm : ∀ g g', τ g * τ g' = τ g' * τ g := fun g g' => by
      rw [← map_mul, ← map_mul, mul_comm]
    have htriv : ∀ (g : Fin 3 → Multiplicative (ZMod p)) (m : Fin 3), g m = 1 →
        ∀ u ∈ Fr.U m, τ g u = u := by
      intro g m hgm u hu
      rw [hτF]
      refine Fr.triv _ m ?_ u hu
      rw [OrthTorus.piMul_apply, toAdd_ofAdd]
      simp [hgm]
    let τΩ : (Fin 3 → Multiplicative (ZMod p)) → ↥(orthDerived Q) := fun g => ⟨τ g, hτΩ g⟩
    have hτΩmul : ∀ g g', τΩ (g * g') = τΩ g * τΩ g' := fun g g' => Subtype.ext (map_mul τ g g')
    have hτΩpow : ∀ g (n : ℕ), τΩ (g ^ n) = τΩ g ^ n := fun g n =>
      Subtype.ext (by simp [τΩ, map_pow])
    have hℓτ : ∀ b', ℓΩ b' = τΩ (c b') := fun b' => Subtype.ext (hc b').symm
    have hcoordeq : ∀ g g' : Fin 3 → Multiplicative (ZMod p), (∀ m, toAdd (g m) = toAdd (g' m)) →
        g = g' := fun g g' h => funext fun m => toAdd.injective (h m)
    have htoAdd_pow : ∀ (g : Fin 3 → Multiplicative (ZMod p)) (n : ℕ) (m : Fin 3),
        toAdd ((g ^ n) m) = (n : ZMod p) * toAdd (g m) := by
      intro g n m
      rw [Pi.pow_apply, toAdd_pow, nsmul_eq_mul]
    have htoAdd_mul : ∀ (g g' : Fin 3 → Multiplicative (ZMod p)) (m : Fin 3),
        toAdd ((g * g') m) = toAdd (g m) + toAdd (g' m) := by
      intro g g' m
      rw [Pi.mul_apply, toAdd_mul]
    have htoAdd_single : ∀ (m m' : Fin 3) (t : ZMod p),
        toAdd ((Pi.mulSingle m (ofAdd t) : Fin 3 → Multiplicative (ZMod p)) m') =
          if m' = m then t else 0 := by
      intro m m' t
      by_cases h : m' = m
      · subst h
        simp
      · simp [Pi.mulSingle_eq_of_ne h, h]
    rcases OmPlusFrame.spAct_reflection_cases hp2 hε h2 hcardFx with
      ⟨rfl, j, hj, hi⟩ | ⟨i, j, k, hij, hik, hjk, hiπ, hjπ, hkπ, hεjk, hεi⟩
    ·
      have hfixj : ∀ b' : ↥Bs, φ b' = b' → cv b' j = 0 := by
        intro b' hb'
        have := congrFun ((hfixiff b').mp hb') j
        rw [OmPlusFrame.spAct_one_apply, hj, neg_one_mul] at this
        have h2' : 2 * cv b' j = 0 := by linear_combination -this
        exact (mul_eq_zero.mp h2').resolve_left (OmPlusFrame.two_ne_zero_zmod hp2)
      have hgenkl : ∀ k l : Fin 3, k ≠ l → k ≠ j → l ≠ j → ∀ b' : ↥Bs, φ b' = b' → ∃ m n : ℕ,
          ℓΩ b' = τΩ (Pi.mulSingle k (ofAdd 1)) ^ m * τΩ (Pi.mulSingle l (ofAdd 1)) ^ n := by
        intro k l hkl hkj hlj b' hb'
        refine ⟨(cv b' k).val, (cv b' l).val, ?_⟩
        rw [hℓτ, ← hτΩpow, ← hτΩpow, ← hτΩmul]
        refine congrArg τΩ ?_
        apply hcoordeq
        intro m
        rw [htoAdd_mul, htoAdd_pow, htoAdd_pow, htoAdd_single, htoAdd_single, ZMod.natCast_zmod_val,
          ZMod.natCast_zmod_val]
        rcases OmPlusFrame.fin_three_cases hkl hkj hlj m with rfl | rfl | rfl
        · simp [hkl, cv]
        · simp [Ne.symm hkl, cv]
        · have h0 := hfixj b' hb'
          simp [Ne.symm hkj, Ne.symm hlj]
          exact h0
      have hfixed_single : ∀ m : Fin 3, ε m = 1 → ∃ bm : ↥Bs, φ bm = bm ∧
          ℓΩ bm = τΩ (Pi.mulSingle m (ofAdd 1)) := by
        intro m hm
        obtain ⟨bm, hbm⟩ := hcvsurj (Pi.single m 1)
        refine ⟨bm, (hfixiff bm).mpr ?_, ?_⟩
        · rw [hbm]
          funext m'
          rw [OmPlusFrame.spAct_one_apply]
          by_cases h : m' = m
          · subst h
            rw [Pi.single_eq_same, hm, mul_one]
          · rw [Pi.single_eq_of_ne h, mul_zero]
        · rw [hℓτ]
          refine congrArg τΩ ?_
          apply hcoordeq
          intro m'
          rw [htoAdd_single]
          have := congrFun hbm m'
          simp only [cv] at this
          rw [this]
          by_cases h : m' = m
          · subst h
            simp
          · simp [h]
      obtain ⟨k, l, hkl, hkj, hlj⟩ : ∃ k l : Fin 3, k ≠ l ∧ k ≠ j ∧ l ≠ j :=
        (by decide : ∀ j : Fin 3, ∃ k l : Fin 3, k ≠ l ∧ k ≠ j ∧ l ≠ j) j
      have hεk := hi k hkj
      have hεl := hi l hlj
      obtain ⟨hN, hsimp, hnab, hcardN⟩ := OmPlusFrame.sign_rankOne hQnd hdim8 hminus hp hp2 hpqF
        (hτΩ (Pi.mulSingle k (ofAdd 1))) (hτΩ (Pi.mulSingle l (ofAdd 1))) (hτcomm _ _)
        (hτpow _) (hτpow _) (by rw [hcU k 1 one_ne_zero, hU2]) (by rw [hcU l 1 one_ne_zero, hU2])
        (by rw [hcU k 1 one_ne_zero]; exact htriv _ k (Pi.mulSingle_eq_of_ne hkl _))
        (by rw [hcU l 1 one_ne_zero]; exact htriv _ l (Pi.mulSingle_eq_of_ne (Ne.symm hkl) _))
      obtain ⟨e0⟩ := ggRankOneIn_equiv_native hψΩinj hψΩrange hcompat (hgenkl k l hkl hkj hlj)
        (hfixed_single k hεk) (hfixed_single l hεl)
      have e := e0.trans (MulEquiv.subgroupCongr hN)
      have hS : IsSimpleGroup ↥(ggRankOneIn X Bs φ) := by
        haveI := hsimp
        haveI : Nontrivial ↥(ggRankOneIn X Bs φ) := e.toEquiv.nontrivial
        exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
      have hnab' : ∃ g h : ↥(ggRankOneIn X Bs φ), g * h ≠ h * g := by
        obtain ⟨g, h, hgh⟩ := hnab
        refine ⟨e.symm g, e.symm h, fun h' => hgh ?_⟩
        have := congrArg e h'
        simpa using this
      refine ⟨@ggIsQuasisimple_of_simple _ _ hS hnab', fun _ => ⟨?_, j, hj, hi,
        fun k' l' hkl' hkj' hlj' => ggRankOneIn_eq_map_native hψΩinj hψΩrange hcompat
          (hgenkl k' l' hkl' hkj' hlj') (hfixed_single k' (hi k' hkj'))
          (hfixed_single l' (hi l' hlj'))⟩, fun h => absurd rfl h⟩
      rw [Nat.card_congr e.toEquiv, hcardN, hF]
    ·
      set η := ε j with hηdef
      have hη : η = 1 ∨ η = -1 := hε j
      have hcoordv : ∀ v : Fin 3 → ZMod p, OmPlusFrame.spAct π ε v k = η * v j ∧
          OmPlusFrame.spAct π ε v j = η * v k ∧ OmPlusFrame.spAct π ε v i = v i := by
        intro v
        refine ⟨OmPlusFrame.spAct_apply_of_eq hjπ ε v, ?_, ?_⟩
        · rw [OmPlusFrame.spAct_apply_of_eq hkπ ε v, ← hεjk]
        · rw [OmPlusFrame.spAct_apply_of_eq hiπ ε v, hεi, one_mul]
      have hηη : η * η = 1 := by rcases hη with h | h <;> rw [h] <;> ring
      have hgen : ∀ b' : ↥Bs, φ b' = b' → ∃ m n : ℕ,
          ℓΩ b' = τΩ (Pi.mulSingle i (ofAdd 1)) ^ m *
            τΩ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd η)) ^ n := by
        intro b' hb'
        have hfx := (hfixiff b').mp hb'
        have hvk : cv b' k = η * cv b' j := by
          have := congrFun hfx k
          rw [(hcoordv _).1] at this
          exact this.symm
        refine ⟨(cv b' i).val, (cv b' j).val, ?_⟩
        rw [hℓτ, ← hτΩpow, ← hτΩpow, ← hτΩmul]
        refine congrArg τΩ ?_
        apply hcoordeq
        intro m
        rw [htoAdd_mul, htoAdd_pow, htoAdd_pow, htoAdd_mul, htoAdd_single, htoAdd_single,
          htoAdd_single, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        rcases OmPlusFrame.fin_three_cases hij hik hjk m with rfl | rfl | rfl
        · simp [hij, hik, cv]
        · simp [Ne.symm hij, hjk, cv]
        · simp only [cv] at hvk
          simp [Ne.symm hik, Ne.symm hjk]
          rw [hvk]
          ring
      have hba : ∃ ba : ↥Bs, φ ba = ba ∧ ℓΩ ba = τΩ (Pi.mulSingle i (ofAdd 1)) := by
        obtain ⟨ba, hba⟩ := hcvsurj (Pi.single i 1)
        refine ⟨ba, (hfixiff ba).mpr ?_, ?_⟩
        · rw [hba]
          funext m
          rcases OmPlusFrame.fin_three_cases hij hik hjk m with rfl | rfl | rfl
          · rw [(hcoordv _).2.2]
          · rw [(hcoordv _).2.1, Pi.single_eq_of_ne (Ne.symm hik), Pi.single_eq_of_ne (Ne.symm hij),
              mul_zero]
          · rw [(hcoordv _).1, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne (Ne.symm hik),
              mul_zero]
        · rw [hℓτ]
          refine congrArg τΩ ?_
          apply hcoordeq
          intro m
          rw [htoAdd_single]
          have := congrFun hba m
          simp only [cv] at this
          rw [this]
          by_cases h : m = i
          · subst h
            simp
          · simp [h]
      have hbs : ∃ bs : ↥Bs, φ bs = bs ∧
          ℓΩ bs = τΩ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd η)) := by
        obtain ⟨bs, hbs⟩ := hcvsurj (fun m => if m = j then 1 else if m = k then η else 0)
        refine ⟨bs, (hfixiff bs).mpr ?_, ?_⟩
        · rw [hbs]
          funext m
          rcases OmPlusFrame.fin_three_cases hij hik hjk m with rfl | rfl | rfl
          · rw [(hcoordv _).2.2]
          · rw [(hcoordv _).2.1]
            simp [hjk, Ne.symm hjk, hηη]
          · rw [(hcoordv _).1]
            simp [hjk, Ne.symm hjk]
        · rw [hℓτ]
          refine congrArg τΩ ?_
          apply hcoordeq
          intro m
          rw [htoAdd_mul, htoAdd_single, htoAdd_single]
          have := congrFun hbs m
          simp only [cv] at this
          rw [this]
          rcases OmPlusFrame.fin_three_cases hij hik hjk m with rfl | rfl | rfl
          · simp [hij, hik]
          · simp [hjk]
          · simp [Ne.symm hjk]
      obtain ⟨hcs, hcs4, h, hh, hne, hm, hVh⟩ := OmPlusFrame.primary_of_pair hQnd hp hp2 hK1 hEΩ
        hpowE hτrange hτF hD2 hcp hcfix hctw hθinj hθrange hθact hU2 hcU hjk hη
      have hsa : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace (τ (Pi.mulSingle i (ofAdd 1))),
          τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd η)) v = v := by
        rw [hcU i 1 one_ne_zero]
        refine htriv _ i ?_
        rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hij, Pi.mulSingle_eq_of_ne hik, mul_one]
      have has' : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace
          (τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd η))),
          τ (Pi.mulSingle i (ofAdd 1)) v = v := by
        rw [hcs]
        intro v hv
        obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add, htriv _ j (Pi.mulSingle_eq_of_ne (Ne.symm hij) _) v₁ hv₁,
          htriv _ k (Pi.mulSingle_eq_of_ne (Ne.symm hik) _) v₂ hv₂]
      obtain ⟨hN, E, _, _, hEcard, ⟨eE⟩⟩ := OmPlusFrame.transp_rankOne hQnd hdim8 hp hp2 hpqF hK4
        (hτΩ _) (hτΩ _) (hτcomm _ _) (hτpow _) (hτpow _) (by rw [hcU i 1 one_ne_zero, hU2]) hcs4
        hsa has' hh hne hm hVh
      obtain ⟨e0⟩ := ggRankOneIn_equiv_native hψΩinj hψΩrange hcompat hgen hba hbs
      have e := e0.trans (MulEquiv.subgroupCongr hN)
      have hE4 : 4 ≤ Nat.card E := hEcard ▸ hK4
      have hSL : CFSG.Assembly.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) E) :=
        ⟨(CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ hE4).commutator_eq_top,
          Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4⟩
      refine ⟨CFSG.Assembly.IsQuasisimple.of_mulEquiv (e.trans eE) hSL, fun h' => ?_, fun _ =>
        ⟨?_, i, j, k, hij, hik, hjk, hiπ, hjπ, hkπ, hεjk, hεi, h, hne, hh,
          ggRankOneIn_eq_map_native hψΩinj hψΩrange hcompat hgen hba hbs, ?_, ?_⟩⟩
      · rw [h', Equiv.Perm.one_apply] at hjπ
        exact absurd hjπ hjk
      · rw [Nat.card_congr (e.trans eE).toEquiv,
          CFSG.LieType.BorelTits.card_specialLinearGroup_fin_two (hEcard.trans hF)]
      · rw [map_subtype_ggOTwoPrime_centralizer]
        exact hN
      · show CFSG.RankThree.PartOne.LIT.commSpace (τ _) =
          CFSG.RankThree.PartOne.LIT.commSpace (τ _) ⊔ CFSG.RankThree.PartOne.LIT.commSpace (τ _)
        rw [hcs, hcU j 1 one_ne_zero, hcU k 1 one_ne_zero]
  have hkerΩ : Nat.card ↥ℓΩ.ker = p := by
    have h1 : ℓΩ.ker = ℓ.ker := by
      ext b
      simp only [MonoidHom.mem_ker, ℓΩ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact ⟨fun h => ι.injective (h.trans (map_one ι).symm), fun h => by
        show ι (ℓ b) = 1
        rw [h]
        exact map_one ι⟩
    rw [h1, ← hZX, ← hkerℓ, Subgroup.card_map_of_injective Bs.subtype_injective]
  have hAind : ggAutomizer X Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hinj : ∀ ψ' ∈ ggAutomizer X Bs, (∀ b, cv (ψ' b) = cv b) → ψ' = 1 := by
    intro ψ' hψ' htriv
    have hkψ := (hA hψ').2
    let δ : ↥Bs →* ↥Bs :=
      { toFun := fun b => ψ' b * b⁻¹
        map_one' := by simp
        map_mul' := fun b b' => by
          rw [map_mul, mul_inv_rev]
          show ψ' b * ψ' b' * (b'⁻¹ * b⁻¹) = ψ' b * b⁻¹ * (ψ' b' * b'⁻¹)
          rw [mul_assoc (ψ' b) (ψ' b'), mul_assoc (ψ' b) b⁻¹]
          exact congrArg (ψ' b * ·)
            ((mul_assoc (ψ' b') b'⁻¹ b⁻¹).symm.trans (hcommBs (ψ' b' * b'⁻¹) b⁻¹)) }
    have hδ : ∀ b, ℓΩ (δ b) = 1 := fun b => (hcv0 _).mp (by
      funext i
      have := congrFun (htriv b) i
      simp only [cv] at this ⊢
      show toAdd (c (ψ' b * b⁻¹) i) = 0
      rw [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, toAdd_mul, toAdd_inv, this, add_neg_cancel])
    have hrangeδ : δ.range ≤ ℓΩ.ker := by
      rintro _ ⟨b, rfl⟩
      exact hδ b
    have hcardδ : Nat.card ↥δ.range = 1 ∨ Nat.card ↥δ.range = p := by
      have hdvd : Nat.card ↥δ.range ∣ p := by
        rw [← hkerΩ]
        exact Subgroup.card_dvd_of_le hrangeδ
      exact (Nat.dvd_prime hp).mp hdvd
    rcases hcardδ with h1 | hpδ
    · ext b
      have hb : δ b = 1 := by
        have := (Subgroup.card_eq_one.mp h1)
        have hmem : δ b ∈ δ.range := ⟨b, rfl⟩
        rw [this] at hmem
        exact hmem
      have hb' : ψ' b * b⁻¹ = 1 := hb
      rw [MulAut.one_apply]
      exact congrArg Subtype.val (mul_inv_eq_one.mp hb')
    · exfalso
      apply hNT ψ' (hAind hψ')
      refine ⟨?_, fun b => ?_⟩
      · have hmul := Subgroup.card_ker_mul_card_range δ
        rw [hpδ] at hmul
        rw [← hmul]
        congr 1
        exact Nat.card_congr (Equiv.subtypeEquivRight fun b => by
          rw [MonoidHom.mem_ker]
          exact ⟨fun h => mul_inv_eq_one.mp (show ψ' b * b⁻¹ = 1 from h),
            fun h => (show ψ' b * b⁻¹ = 1 from mul_inv_eq_one.mpr h)⟩).symm
      · have h1 : b⁻¹ * ψ' b = δ b := by
          show b⁻¹ * ψ' b = ψ' b * b⁻¹
          exact hcommBs _ _
        rw [h1]
        exact hkψ _ (hδ b)
  refine ⟨Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f, inferInstance, inferInstance,
    inferInstance, Q, ψΩ, τh, cv, hQnd, hψΩinj, hψΩrange, ?_, ?_, hcvsurj, ?_, ?_, hinj, hper⟩
  ·
    have hcardR : Nat.card ℓ.range = p ^ 3 := by
      have h1 : Nat.card (ℓΩ.range.map (orthDerived Q).subtype) = Nat.card ℓ.range := by
        rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective]
        have hr : ℓΩ.range = ℓn.range.map ι.toMonoidHom := MonoidHom.range_comp _ _
        rw [hr, Subgroup.card_map_of_injective ι.injective]
        rfl
      rw [← h1, ← hτrange, ← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, Nat.card_fun]
      have hZ : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
      rw [hZ, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    have hker' : Nat.card ℓ.ker = Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
      rw [← hkerℓ, Subgroup.card_map_of_injective Bs.subtype_injective]
    rw [← Subgroup.card_ker_mul_card_range ℓ, hker', hcardR, mul_comm]
  · intro b b'
    funext i
    show toAdd (c (b * b') i) = toAdd (c b i) + toAdd (c b' i)
    rw [map_mul, Pi.mul_apply, toAdd_mul]
  · intro m
    show finrank (GaloisField 2 f)
      (CFSG.RankThree.PartOne.LIT.commSpace (τ (Pi.mulSingle m (ofAdd 1)))) = 2
    rw [hcU m 1 one_ne_zero, hU2]
  · intro φ hφ
    obtain ⟨⟨π, ε, hε, hcφ⟩, -⟩ := hA hφ
    exact ⟨π, ε, hε, hcv_act hcφ⟩
set_option maxHeartbeats 2000000 in
theorem plusMember_facts {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    (hp : p.Prime) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) {ψ : (ggU .POmegaMinus 4 f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K) (hrange : ψ.range = X)
    {ℓ : ↥Bs →* (ggU .POmegaMinus 4 f).K}
    (hℓ : ∀ (b : ↥Bs) (u : (ggU .POmegaMinus 4 f).K),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hkerℓ : ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G))
    (hZX : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p)
    (hrankℓ : p ^ 3 ≤ Nat.card ℓ.range) :
    (∀ φ ∈ ggAutomizer X Bs, GGIsReflection p φ →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs φ) ∧
        (Nat.card ↥(ggRankOneIn X Bs φ) = 2 ^ f * ((2 ^ f) ^ 2 - 1) ∨
          Nat.card ↥(ggRankOneIn X Bs φ) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1))) ∧
    (∀ φ ∈ ggAutomizer X Bs, ∀ φ' ∈ ggAutomizer X Bs, GGIsReflection p φ →
      GGIsReflection p φ' → φ ≠ φ' → (φ * φ') ^ 3 = 1 →
        Nat.card ↥(ggRankOneIn X Bs φ) = 2 ^ f * ((2 ^ f) ^ 2 - 1)) ∧
    (∀ φ ∈ ggAutomizer X Bs, ∀ φ' ∈ ggAutomizer X Bs, GGIsReflection p φ →
      GGIsReflection p φ' → (φ * φ') ^ 4 = 1 → (φ * φ') ^ 2 ≠ 1 →
        (Nat.card ↥(ggRankOneIn X Bs φ) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) ↔
          Nat.card ↥(ggRankOneIn X Bs φ') = 2 ^ f * ((2 ^ f) ^ 2 - 1))) ∧
    Nat.card ↥Bs = p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, _, _, _, Q, ψΩ, τ, cv, -, -, -, hcardBs, -, hcvsurj, -, hA, hinj, hper⟩ :=
    plusMember_native hp hBs hNT hf hpq hker hrange hℓ hkerℓ hZX hrankℓ
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsb : 2 ^ f * ((2 ^ f) ^ 2 - 1) ≠ (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) := by
    have hq : 4 ≤ 2 ^ f := hF ▸ hK4
    generalize 2 ^ f = q at hq ⊢
    have hq4 : q + 1 < q ^ 4 := by
      calc q + 1 < q * 4 := by omega
        _ ≤ q * q ^ 3 := Nat.mul_le_mul_left _ (hq.trans (Nat.le_self_pow (by norm_num) q))
        _ = q ^ 4 := by ring
    have hlt : q < q ^ 4 - 1 := by omega
    have h3 : q * (q ^ 2 - 1) < q ^ 2 * (q ^ 4 - 1) :=
      calc q * (q ^ 2 - 1) ≤ q * q ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = q ^ 2 * q := by ring
        _ < q ^ 2 * (q ^ 4 - 1) := mul_lt_mul_of_pos_left hlt (by positivity)
    exact ne_of_lt h3
  have hinv : ∀ φ ∈ ggAutomizer X Bs, GGIsReflection p φ →
      ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p),
      (∀ b, cv (φ b) = OmPlusFrame.spAct π ε (cv b)) → π * π = 1 := by
    intro φ _ hφ π ε hcvφ
    apply OmPlusFrame.perm_eq_one_of_spAct (p := p)
    refine ⟨fun i => ε (π i) * ε i, fun v => ?_⟩
    obtain ⟨b, rfl⟩ := hcvsurj v
    rw [← OmPlusFrame.spAct_spAct, ← hcvφ, ← hcvφ, ← MulAut.mul_apply, ← pow_two, hφ.1,
      MulAut.one_apply]
  have hpowcv : ∀ (φ φ' : MulAut ↥Bs) (π π' : Equiv.Perm (Fin 3)) (ε ε' : Fin 3 → ZMod p),
      (∀ b, cv (φ b) = OmPlusFrame.spAct π ε (cv b)) →
      (∀ b, cv (φ' b) = OmPlusFrame.spAct π' ε' (cv b)) → ∀ (n : ℕ) (b : ↥Bs),
      cv (((φ * φ') ^ n) b) =
        (fun w => OmPlusFrame.spAct π ε (OmPlusFrame.spAct π' ε' w))^[n] (cv b) := by
    intro φ φ' π π' ε ε' h h' n
    induction n with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply, h, h', ih, Function.iterate_succ_apply']
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ hφL hφ
    obtain ⟨π, ε, hε, hcφ⟩ := hA φ hφL
    obtain ⟨hq, h1, h2⟩ := hper φ hφL hφ π ε hε hcφ
    refine ⟨hq, ?_⟩
    by_cases hπ : π = 1
    · exact Or.inr (h1 hπ).1
    · exact Or.inl (h2 hπ).1
  · intro φ hφL φ' hφ'L hφ hφ' hne h3
    obtain ⟨π, ε, hε, hcφ⟩ := hA φ hφL
    obtain ⟨π', ε', hε', hcφ'⟩ := hA φ' hφ'L
    obtain ⟨-, -, hsmall⟩ := hper φ hφL hφ π ε hε hcφ
    refine (hsmall ?_).1
    intro hπ1
    have hπ'2 := hinv φ' hφ'L hφ' π' ε' hcφ'
    have h4 : (φ * φ') ^ 4 = 1 := by
      apply hinj _ (pow_mem (mul_mem hφL hφ'L) 4)
      intro b
      rw [hpowcv φ φ' π π' ε ε' hcφ hcφ' 4 b, hπ1]
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact OmPlusFrame.spAct_four_of_diag hε hε' hπ'2 _
    have h1 : φ * φ' = 1 := by
      have : (φ * φ') ^ 4 = (φ * φ') ^ 3 * (φ * φ') := pow_succ _ 3
      rw [h4, h3, one_mul] at this
      exact this.symm
    apply hne
    have hφ'i : φ'⁻¹ = φ' := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hφ'.1)
    rw [← hφ'i]
    exact eq_inv_of_mul_eq_one_left h1
  · intro φ hφL φ' hφ'L hφ hφ' h4 h2
    obtain ⟨π, ε, hε, hcφ⟩ := hA φ hφL
    obtain ⟨π', ε', hε', hcφ'⟩ := hA φ' hφ'L
    obtain ⟨-, hbig, hsmall⟩ := hper φ hφL hφ π ε hε hcφ
    obtain ⟨-, hbig', hsmall'⟩ := hper φ' hφ'L hφ' π' ε' hε' hcφ'
    have hπ2 := hinv φ hφL hφ π ε hcφ
    have hπ'2 := hinv φ' hφ'L hφ' π' ε' hcφ'
    have key : π = 1 ↔ π' ≠ 1 := by
      constructor
      · intro hπ hπ'
        apply h2
        apply hinj _ (pow_mem (mul_mem hφL hφ'L) 2)
        intro b
        rw [hpowcv φ φ' π π' ε ε' hcφ hcφ' 2 b, hπ, hπ']
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
        exact OmPlusFrame.spAct_sq_of_diag hε hε' _
      · intro hπ'
        by_contra hπ
        apply h2
        have h6 : (φ * φ') ^ 6 = 1 := by
          apply hinj _ (pow_mem (mul_mem hφL hφ'L) 6)
          intro b
          rw [hpowcv φ φ' π π' ε ε' hcφ hcφ' 6 b]
          exact OmPlusFrame.spAct_six_of_swaps hε hε' hπ2 hπ hπ'2 hπ' _
        have : (φ * φ') ^ 6 = (φ * φ') ^ 4 * (φ * φ') ^ 2 := by rw [← pow_add]
        rw [h6, h4, one_mul] at this
        exact this.symm
    constructor
    · intro hb
      have hπ : π = 1 := by
        by_contra hπ
        exact hsb ((hsmall hπ).1.symm.trans hb)
      exact (hsmall' (key.mp hπ)).1
    · intro hs
      have hπ' : π' ≠ 1 := by
        intro hπ'
        exact hsb (hs.symm.trans (hbig' hπ').1)
      exact (hbig (key.mpr hπ')).1
  · exact hcardBs

theorem plusMember_facts_of_image (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs X : Subgroup G} (hp : p.Prime) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) (hBs4 : p ^ 4 ≤ Nat.card ↥Bs) {f : ℕ} (hf : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hmark : GGCentralImage .POmegaMinus 4 f X)
    (hInn : GGInnerDiagOn Bs X)
    (hZX : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p) :
    (∀ φ ∈ ggAutomizer X Bs, GGIsReflection p φ →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs φ) ∧
        (Nat.card ↥(ggRankOneIn X Bs φ) = 2 ^ f * ((2 ^ f) ^ 2 - 1) ∨
          Nat.card ↥(ggRankOneIn X Bs φ) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1))) ∧
    (∀ φ ∈ ggAutomizer X Bs, ∀ φ' ∈ ggAutomizer X Bs, GGIsReflection p φ →
      GGIsReflection p φ' → φ ≠ φ' → (φ * φ') ^ 3 = 1 →
        Nat.card ↥(ggRankOneIn X Bs φ) = 2 ^ f * ((2 ^ f) ^ 2 - 1)) ∧
    (∀ φ ∈ ggAutomizer X Bs, ∀ φ' ∈ ggAutomizer X Bs, GGIsReflection p φ →
      GGIsReflection p φ' → (φ * φ') ^ 4 = 1 → (φ * φ') ^ 2 ≠ 1 →
        (Nat.card ↥(ggRankOneIn X Bs φ) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) ↔
          Nat.card ↥(ggRankOneIn X Bs φ') = 2 ^ f * ((2 ^ f) ^ 2 - 1))) ∧
    Nat.card ↥Bs = p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  let : IsMulCommutative ↥Bs := hBs.1
  obtain ⟨ψ, hadm, hker, hrange⟩ := hmark
  have hrk : 2 ≤ (ggU .POmegaMinus 4 f).D.rank :=
    two_le_lieUniversal_rank .POmegaMinus 4 2 f Nat.prime_two hadm (by decide)
  obtain ⟨_, lab, _, hraw⟩ := hMp G .POmegaMinus 4 f ψ hadm hrk hker X hrange _ hInn
  obtain ⟨R, _, I, _, _, _, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 f
  let ψn : ↥(spinGroup (Spin.quadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) →* G := ψ
  have hdiag' : ∀ b ∈ Bs, GGPsiInnerDiag
      (Spin.Twisted.minusDatum 4 (minusCoeffs_irr 2 f)) ψn b :=
    fun b hb => himp b (hBsN hb) (hI b hb)
  have hcard' : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψn.range : Set G)) ≤
      Nat.card Bs := by
    rw [show ψn.range = X from hrange, hZX, ← pow_succ]
    exact hBs4
  obtain ⟨ℓ, hℓ, hkerℓ, -, hrankℓ⟩ := F4KGPosition.exists_spinMinus_lift_kernel_rank
    4 (minusCoeffs_irr 2 f) (by decide) ψn hker Bs hdiag' hBs.2 hcard'
  rw [show ψn.range = X from hrange] at hkerℓ
  exact plusMember_facts hp hBs hNT hf hpq hker hrange hℓ hkerℓ hZX hrankℓ

theorem ggOppPlus_rankOne_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGCentralImage .POmegaMinus 4 f L) {φ : MulAut ↥Bs}
    (hφL : φ ∈ ggAutomizer L Bs) (hφ : GGIsReflection p φ) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs φ) ∧ p ∣ Nat.card ↥(ggRankOneIn L Bs φ) := by
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hc.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hZL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hc.bstar_inf_centralizer_L, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2 x hxBs) hc.1.2.2.2.2.2.2.1.2.2.1]
  obtain ⟨ψ, hker, hrange, ℓ, hℓ, hkerℓ, -, hrankℓ⟩ :=
    F4KGPosition.exists_spinMinus_lifts_of_f4_member ggInnerDiagMpInput_holds hcfg (Or.inl rfl)
      hmark
  obtain ⟨h1, -, -, -⟩ := plusMember_facts hp hBs hcfg.1.2.2.2.1 hf hpq hker hrange hℓ hkerℓ hZL
    hrankℓ
  obtain ⟨hq, hcard⟩ := h1 φ hφL hφ
  refine ⟨hq, ?_⟩
  have hq2 : 2 ^ f + 1 ∣ (2 ^ f) ^ 2 - 1 := by
    rw [show (2 ^ f) ^ 2 - 1 = (2 ^ f) ^ 2 - 1 ^ 2 by norm_num, Nat.sq_sub_sq]
    exact dvd_mul_right _ _
  have hq4 : (2 ^ f) ^ 2 - 1 ∣ (2 ^ f) ^ 4 - 1 := by
    have h := Nat.sub_one_dvd_pow_sub_one ((2 ^ f) ^ 2) 2
    rwa [show ((2 ^ f) ^ 2) ^ 2 = (2 ^ f) ^ 4 by ring] at h
  rcases hcard with h | h <;> rw [h]
  · exact Dvd.dvd.mul_left (hpq.trans hq2) _
  · exact Dvd.dvd.mul_left (hpq.trans (hq2.trans hq4)) _

end Main

end CFSG.StandardType

end
