module

public import CFSG.LinearAlgebra.TwoGroupNormalizerLargePrime
public import CFSG.Quasithin.Vol2.Ch11SecS12ZF
public import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN

open Subgroup Module
open CFSG.SectionRank.Ccomm
open scoped commutatorElement

theorem conj_action_eq_on_weightSpace {K V Γ : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Γ] [Finite Γ]
    {ρ : Representation K Γ V} {Z C : Subgroup Γ} {r : ℕ} (hr : r.Prime)
    (h2 : (2 : K) ≠ 0)
    (hZC : ∀ n ∈ Z, ∀ c ∈ C, n * c = c * n)
    (hcommZ : ∀ a ∈ C, ∀ b ∈ C, a⁻¹ * b⁻¹ * a * b ∈ Z)
    (hC2 : IsPGroup 2 C)
    (hfin : ∀ χ : Z → K, finrank K (CFSG.Walter.JT.weightSpace ρ Z χ →ₗ[K]
      CFSG.Walter.JT.weightSpace ρ Z χ) < r)
    {y : Γ} (hyZc : ∀ n ∈ Z, y * n = n * y) (hyC : y ∈ normalizer (C : Set Γ))
    {k : ℕ} (hyk : y ^ r ^ k = 1) :
    ∀ (χ : Z → K) (z : Γ), z ∈ C → ∀ c ∈ C,
      ∀ v ∈ CFSG.Walter.JT.weightSpace ρ Z χ,
      ρ ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹) v = ρ (z * c * z⁻¹) v := by
  classical
  set H : Subgroup Γ := centralizer (Z : Set Γ) with hHdef
  have hyH : y ∈ H := mem_centralizer_iff.mpr fun n hn => (hyZc n hn).symm
  have hCH : C ≤ H := fun c hc => mem_centralizer_iff.mpr fun n hn => hZC n hn c hc
  have hmaps : ∀ (χ : Z → K) (h : H), ∀ v ∈ CFSG.Walter.JT.weightSpace ρ Z χ,
      ρ h v ∈ CFSG.Walter.JT.weightSpace ρ Z χ := by
    intro χ h v hv
    rw [CFSG.Walter.JT.mem_weightSpace] at hv ⊢
    intro n
    have hnh : (n : Γ) * h = h * n := mem_centralizer_iff.mp h.2 n n.2
    rw [← Module.End.mul_apply, ← map_mul, hnh, map_mul, Module.End.mul_apply, hv n, map_smul]
  intro χ z hz c hc v hv
  set W := CFSG.Walter.JT.weightSpace ρ Z χ with hW
  let σ : Representation K H W :=
    Representation.subrepresentation (ρ.comp H.subtype) W (fun g w hw => hmaps χ g w hw)
  have hσ : ∀ (g : H) (w : W), ((σ g w : W) : V) = ρ g w := fun _ _ => rfl
  let Ad : Representation K H (W →ₗ[K] W) := σ.linHom σ
  have hAd : ∀ (g : H) (T : W →ₗ[K] W) (w : W), Ad g T w = σ g (T (σ g⁻¹ w)) :=
    fun _ _ _ => rfl
  have hAdZ : ∀ (n : H), (n : Γ) ∈ Z → Ad n = 1 := by
    intro n hn
    have hs : ∀ (m : Γ) (hm : m ∈ Z) (u : V), u ∈ W → ρ m u = χ ⟨m, hm⟩ • u :=
      fun m hm u hu => (CFSG.Walter.JT.mem_weightSpace.mp hu) ⟨m, hm⟩
    have hn' : ((n : Γ))⁻¹ ∈ Z := Z.inv_mem hn
    have hinvσ : ∀ w : W, σ n⁻¹ w = χ ⟨_, hn'⟩ • w := fun w =>
      Subtype.ext (by rw [hσ]; exact hs _ hn' w w.2)
    have hσn : ∀ w : W, σ n w = χ ⟨_, hn⟩ • w := fun w =>
      Subtype.ext (by rw [hσ]; exact hs _ hn w w.2)
    have hab : ∀ w : W, (χ ⟨_, hn⟩ * χ ⟨_, hn'⟩) • w = w := by
      intro w
      have h1 : σ n (σ n⁻¹ w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [hinvσ, map_smul, hσn, smul_smul, mul_comm] at h1
      exact h1
    refine LinearMap.ext fun T => LinearMap.ext fun w => ?_
    rw [hAd, hinvσ, map_smul, map_smul, hσn, smul_smul, mul_comm (χ _) (χ _), ← map_smul, hab]
    rfl
  have hAdcomm : ∀ a ∈ C.subgroupOf H, ∀ b ∈ C.subgroupOf H, Ad a * Ad b = Ad b * Ad a := by
    intro a ha b hb
    have hn := hcommZ a (mem_subgroupOf.mp ha) b (mem_subgroupOf.mp hb)
    have hnH : (a : Γ)⁻¹ * (b : Γ)⁻¹ * a * b ∈ H := H.mul_mem (H.mul_mem (H.mul_mem
      (H.inv_mem a.2) (H.inv_mem b.2)) a.2) b.2
    have he : a * b = b * a * ⟨(a : Γ)⁻¹ * (b : Γ)⁻¹ * a * b, hnH⟩ := Subtype.ext (by
      show (a : Γ) * b = b * a * ((a : Γ)⁻¹ * (b : Γ)⁻¹ * a * b)
      group)
    rw [← map_mul, ← map_mul, he, map_mul, hAdZ ⟨_, hnH⟩ hn, mul_one]
  have hCchar : ((Nat.card (C.subgroupOf H) : ℕ) : K) ≠ 0 :=
    CFSG.LinearAlgebra.TwoGroupNormalizer.natCast_card_ne_zero h2
      (hC2.comap_subtype (K := H))
  have hfin' : finrank K (W →ₗ[K] W) < r := hfin χ
  set y' : H := ⟨y, hyH⟩
  have hy'k : y' ^ r ^ k = 1 := Subtype.ext (by simpa using hyk)
  have hRN : zpowers y' ≤ normalizer ((C.subgroupOf H : Subgroup H) : Set H) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro g
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp hyC g
  have hconj := CFSG.Walter.JT.map_conj_eq_of_isPGroup Ad (C.subgroupOf H) hAdcomm hCchar hr
    hfin' (CFSG.LinearAlgebra.TwoGroupNormalizer.isPGroup_zpowers_of_pow_eq_one hy'k) hRN y'
    (mem_zpowers y') ⟨z, hCH hz⟩ (mem_subgroupOf.mpr hz)
  have hT := LinearMap.congr_fun (LinearMap.congr_fun hconj (σ ⟨c, hCH hc⟩)) ⟨v, hv⟩
  have hT' := congrArg Subtype.val hT
  simp only [hAd, hσ] at hT'
  simpa [y', map_mul, Module.End.mul_apply, mul_assoc] using hT'

theorem conj_eq_of_conj_action_eq_on_weightSpace {K V Γ : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Γ] [Finite Γ]
    {ρ : Representation K Γ V} {Z C P : Subgroup Γ} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hZchar : ((Nat.card Z : ℕ) : K) ≠ 0)
    (hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, ρ a * ρ b = ρ b * ρ a)
    (hP2 : IsPGroup 2 P) (hinj : Set.InjOn ρ P) (hCP : C ≤ P)
    (hCcen : ∀ w ∈ C, (∀ c ∈ C, w * c = c * w) → w ∈ Z)
    {y : Γ} (hyZc : ∀ n ∈ Z, y * n = n * y) (hyC : y ∈ normalizer (C : Set Γ))
    {k : ℕ} (hyk : y ^ r ^ k = 1)
    (hkey : ∀ (χ : Z → K) (z : Γ), z ∈ C → ∀ c ∈ C,
      ∀ v ∈ CFSG.Walter.JT.weightSpace ρ Z χ,
      ρ ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹) v = ρ (z * c * z⁻¹) v) :
    ∀ z ∈ C, y * z * y⁻¹ = z := by
  classical
  have hyCm : ∀ c ∈ C, y * c * y⁻¹ ∈ C := fun c hc => (mem_normalizer_iff.mp hyC c).mp hc
  have hPpow : ∀ x ∈ P, ∃ m : ℕ, x ^ 2 ^ m = 1 := fun x hx => by
    obtain ⟨m, hm⟩ := hP2 ⟨x, hx⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have htop := (CFSG.Walter.JT.iSupIndep_weightSpace_and_iSup_eq_top ρ Z hZcomm hZchar).2
  intro z hz
  have haC : y * z * y⁻¹ ∈ C := hyCm z hz
  set w := z⁻¹ * (y * z * y⁻¹) with hwdef
  have hwC : w ∈ C := C.mul_mem (C.inv_mem hz) haC
  have hwc : ∀ c ∈ C, w * c = c * w := by
    intro c hc
    have hle : ∀ χ, CFSG.Walter.JT.weightSpace ρ Z χ ≤ LinearMap.eqLocus
        (ρ ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹)) (ρ (z * c * z⁻¹)) :=
      fun χ v hv => hkey χ z hz c hc v hv
    have h1 : LinearMap.eqLocus (ρ ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹))
        (ρ (z * c * z⁻¹)) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact iSup_le hle
    have h2 := LinearMap.eqLocus_eq_top.mp h1
    have h3 : (y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹ = z * c * z⁻¹ :=
      hinj (hCP (C.mul_mem (C.mul_mem haC hc) (C.inv_mem haC)))
        (hCP (C.mul_mem (C.mul_mem hz hc) (C.inv_mem hz))) h2
    calc w * c = z⁻¹ * ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹) * (y * z * y⁻¹) := by
          rw [hwdef]; group
      _ = z⁻¹ * (z * c * z⁻¹) * (y * z * y⁻¹) := by rw [h3]
      _ = c * w := by rw [hwdef]; group
  have hwZ : w ∈ Z := hCcen w hwC hwc
  have hyw : Commute y w := hyZc w hwZ
  have hiter : ∀ j : ℕ, y ^ j * z * (y ^ j)⁻¹ = z * w ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hyz : y * z * y⁻¹ = z * w := by rw [hwdef]; group
      calc y ^ (j + 1) * z * (y ^ (j + 1))⁻¹ = y * (y ^ j * z * (y ^ j)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = y * z * y⁻¹ * (y * w ^ j * y⁻¹) := by rw [ih]; group
        _ = z * w * w ^ j := by
            rw [hyz, (hyw.pow_right j).eq, mul_inv_cancel_right]
        _ = z * w ^ (j + 1) := by rw [pow_succ', mul_assoc]
  have hwr : w ^ r ^ k = 1 := by
    have := hiter (r ^ k)
    rw [hyk, one_mul, inv_one, mul_one] at this
    exact (mul_eq_left.mp this.symm)
  obtain ⟨m, hm⟩ := hPpow w (hCP hwC)
  have hcop : Nat.Coprime (r ^ k) (2 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hw1 : w = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hwr) (orderOf_dvd_of_pow_eq_one hm))
  calc y * z * y⁻¹ = z * w := by rw [hwdef]; group
    _ = z := by rw [hw1, mul_one]

theorem commute_of_mem_normalizer_of_sq_lt {K V Γ : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Γ] [Finite Γ]
    (h2 : (2 : K) ≠ 0) {d : ℕ} (hd : 2 ≤ d) (hV : finrank K V ≤ d)
    (ρ : Representation K Γ V) {P : Subgroup Γ} (hP : IsPGroup 2 P) (hinj : Set.InjOn ρ P)
    {r : ℕ} (hr : r.Prime) (hdr : d * d < r) {y : Γ} (hy : y ∈ normalizer (P : Set Γ))
    {k : ℕ} (hyk : y ^ r ^ k = 1) : ∀ x ∈ P, y * x = x * y := by
  classical
  have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
  have hVr : finrank K V < r := by omega
  obtain ⟨C₀, hC, -, hcrit⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical hP
  obtain ⟨hchar, -, hcomm, -⟩ := hC
  have := hchar
  set α : MulAut P := P.normalizerMonoidHom ⟨y, hy⟩ with hαdef
  have hα : ∀ x : P, ((α x : P) : Γ) = y * x * y⁻¹ := fun _ => rfl
  set Z₀ : Subgroup P := C₀ ⊓ centralizer (C₀ : Set P) with hZ₀
  have hZ₀char : Z₀.Characteristic := by
    have := CFSG.SectionRank.Ccomm.characteristic_centralizer C₀
    exact CFSG.SectionRank.Ccomm.characteristic_inf _ _
  set C : Subgroup Γ := C₀.map P.subtype with hCdef
  set Z : Subgroup Γ := Z₀.map P.subtype with hZdef
  have hCP : C ≤ P := map_subtype_le _
  have hZP : Z ≤ P := map_subtype_le _
  have memC : ∀ x : P, (x : Γ) ∈ C ↔ x ∈ C₀ := fun x => mem_map_iff_mem P.subtype_injective
  have memZ : ∀ x : P, (x : Γ) ∈ Z ↔ x ∈ Z₀ := fun x => mem_map_iff_mem P.subtype_injective
  have hZC : ∀ n ∈ Z, ∀ c ∈ C, n * c = c * n := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨c, hc, rfl⟩
    have := mem_centralizer_iff.mp hn.2 c hc
    exact congrArg Subtype.val this.symm
  have hZle : Z ≤ C := map_mono inf_le_left
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, ρ a * ρ b = ρ b * ρ a := fun a ha b hb => by
    rw [← map_mul, ← map_mul, hZC a ha b (hZle hb)]
  have hZchar : ((Nat.card Z : ℕ) : K) ≠ 0 :=
    CFSG.LinearAlgebra.TwoGroupNormalizer.natCast_card_ne_zero h2 (hP.to_le hZP)
  have hcommZ : ∀ a ∈ C, ∀ b ∈ C, a⁻¹ * b⁻¹ * a * b ∈ Z := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a⁻¹, b⁻¹⁆ ∈ Z₀ :=
      hcomm (commutator_mem_commutator (mem_top _) (C₀.inv_mem hb))
    have h2 := (memZ _).mpr h1
    simpa [commutatorElement_def] using h2
  have hyC :=
    CFSG.LinearAlgebra.TwoGroupNormalizer.mem_normalizer_map_of_characteristic hy hchar
  have hyZ :=
    CFSG.LinearAlgebra.TwoGroupNormalizer.mem_normalizer_map_of_characteristic hy hZ₀char
  have hstep1 := CFSG.Walter.JT.map_conj_eq_of_isPGroup ρ Z hZcomm hZchar hr hVr
    (CFSG.LinearAlgebra.TwoGroupNormalizer.isPGroup_zpowers_of_pow_eq_one hyk)
    (zpowers_le.mpr hyZ)
  have hyZc : ∀ n ∈ Z, y * n = n * y := by
    intro n hn
    have h1 := hstep1 y (mem_zpowers y) n hn
    have h3 : y * n * y⁻¹ = n :=
      hinj (hZP ((mem_normalizer_iff.mp hyZ n).mp hn)) (hZP hn) h1
    calc y * n = y * n * y⁻¹ * y := by group
      _ = n * y := by rw [h3]
  have hC2 : IsPGroup 2 C := hP.to_le hCP
  have hfin : ∀ χ : Z → K, finrank K (CFSG.Walter.JT.weightSpace ρ Z χ →ₗ[K]
      CFSG.Walter.JT.weightSpace ρ Z χ) < r := by
    intro χ
    rw [Module.finrank_linearMap]
    have hWd : finrank K (CFSG.Walter.JT.weightSpace ρ Z χ) ≤ d :=
      (Submodule.finrank_le _).trans hV
    have hmul : finrank K (CFSG.Walter.JT.weightSpace ρ Z χ) *
        finrank K (CFSG.Walter.JT.weightSpace ρ Z χ) ≤ d * d := Nat.mul_le_mul hWd hWd
    omega
  have hkey := conj_action_eq_on_weightSpace hr h2 hZC hcommZ hC2 hfin hyZc hyC hyk
  have hCcen : ∀ w ∈ C, (∀ c ∈ C, w * c = c * w) → w ∈ Z := by
    intro w hwC hwc
    have hwP : w ∈ P := hCP hwC
    rw [show w = ((⟨w, hwP⟩ : P) : Γ) from rfl, memZ]
    refine ⟨(memC _).mp hwC, mem_centralizer_iff.mpr fun c hc => Subtype.ext ?_⟩
    exact (hwc c ((memC c).mpr hc)).symm
  have hr2 : r ≠ 2 := by
    have h4 : 2 * 2 ≤ d * d := Nat.mul_le_mul hd hd
    omega
  have hCfix := conj_eq_of_conj_action_eq_on_weightSpace hr hr2 hZchar hZcomm hP hinj hCP
    hCcen hyZc hyC hyk hkey
  have hαr : α ^ r ^ k = 1 := by
    rw [hαdef, ← map_pow]
    have : (⟨y, hy⟩ : normalizer (P : Set Γ)) ^ r ^ k = 1 := Subtype.ext (by simpa using hyk)
    rw [this, map_one]
  have hαcop : Nat.Coprime (orderOf α) 2 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hαr)
      (Nat.Coprime.pow_left _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2))
  have hα1 : α = 1 := hcrit α hαcop fun x hx => Subtype.ext (by
    rw [hα]; exact hCfix x ((memC x).mpr hx))
  intro x hx
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hα1 ⟨x, hx⟩)
  rw [hα] at h1
  change y * x * y⁻¹ = x at h1
  calc y * x = y * x * y⁻¹ * y := by group
    _ = x * y := by rw [h1]

theorem commute_of_mem_normalizer_GL {s n : ℕ} [Fact s.Prime] (hs2 : s ≠ 2) (hn : n ≤ 2)
    {P : Subgroup (GL (Fin n) (ZMod s))} (hP : IsPGroup 2 P) {r : ℕ} (hr : r.Prime) (hr4 : 4 < r)
    {y : GL (Fin n) (ZMod s)} (hy : y ∈ normalizer (P : Set (GL (Fin n) (ZMod s))))
    {k : ℕ} (hyk : y ^ r ^ k = 1) : ∀ x ∈ P, y * x = x * y := by
  classical
  let K := AlgebraicClosure (ZMod s)
  let V := Fin n → K
  have halg : Function.Injective (algebraMap (ZMod s) K) :=
    RingHom.injective (algebraMap (ZMod s) K)
  have h2 : (2 : K) ≠ 0 := by
    have hs2' : (2 : ZMod s) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod s) = 0 := by simpa using h
      rw [ZMod.natCast_eq_zero_iff] at h'
      rcases (Nat.dvd_prime Nat.prime_two).mp h' with h1 | h2
      · have := (Fact.out (p := s.Prime)).two_le
        omega
      · exact hs2 h2
    intro h0
    have h1 : algebraMap (ZMod s) K (2 : ZMod s) = 0 := by
      rw [map_ofNat]
      exact h0
    exact hs2' (halg (by rw [h1, map_zero]))
  have hV : finrank K V ≤ 2 := by
    change finrank K (Fin n → K) ≤ 2
    rw [Module.finrank_fin_fun K]
    omega
  let φ : GL (Fin n) (ZMod s) →* GL (Fin n) K :=
    Matrix.GeneralLinearGroup.map (algebraMap (ZMod s) K)
  let e : GL (Fin n) K ≃* (V →ₗ[K] V)ˣ :=
    Matrix.GeneralLinearGroup.toLin
  let ρ : Representation K (GL (Fin n) (ZMod s)) V :=
    (Units.coeHom (V →ₗ[K] V)).comp (e.toMonoidHom.comp φ)
  have hmap : Function.Injective (RingHom.mapMatrix (m := Fin n) (algebraMap (ZMod s) K)) := by
    intro A B h
    ext i j
    refine halg ?_
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) h
    simpa using h1
  have hinjφ : Function.Injective φ := by
    intro A B h
    have h1 : (RingHom.mapMatrix (m := Fin n) (algebraMap (ZMod s) K))
        (A : Matrix (Fin n) (Fin n) (ZMod s)) =
        (RingHom.mapMatrix (m := Fin n) (algebraMap (ZMod s) K))
          (B : Matrix (Fin n) (Fin n) (ZMod s)) := congrArg Units.val h
    exact Units.ext (hmap h1)
  have hinjρ : Function.Injective ρ := by
    intro a b hab
    have h1 : (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)) (φ a) =
        (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)) (φ b) :=
      Units.ext hab
    exact hinjφ ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)).injective h1)
  have hcomm := commute_of_mem_normalizer_of_sq_lt h2 (by norm_num : 2 ≤ 2) hV ρ hP
    (hinjρ.injOn) hr (by omega) hy hyk
  intro x hx
  exact hinjρ (congrArg ρ (hcomm x hx))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_centralizer_of_frattiniAction_eq_one {s t : ℕ} [Fact s.Prime] (ht : t.Prime)
    (hst : s ≠ t) {P X : Subgroup G} (hX : IsPGroup t X)
    (hXP : X ≤ normalizer (P : Set G)) {D : Subgroup ↥P} [D.Characteristic]
    (hker : IsPGroup s (frattiniAction D).ker)
    (hmem : ∀ x (hx : x ∈ X), frattiniAction D (P.normalizerMonoidHom ⟨x, hXP hx⟩) = 1) :
    X ≤ centralizer (P : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hxN : x ∈ normalizer (P : Set G) := hXP hx
  set φx : MulAut ↥P := P.normalizerMonoidHom ⟨x, hxN⟩ with hφx
  have hφx1 : φx = 1 := by
    have hkerx : φx ∈ (frattiniAction D).ker := MonoidHom.mem_ker.mpr (hmem x hx)
    obtain ⟨m, hm⟩ := hX ⟨x, hx⟩
    have htpow : φx ^ t ^ m = 1 := by
      rw [hφx, ← map_pow]
      have h1 : (⟨x, hxN⟩ : normalizer (P : Set G)) ^ t ^ m = 1 :=
        Subtype.ext (by simpa using congrArg (fun y : X => (y : G)) hm)
      rw [h1, map_one]
    obtain ⟨m', hm'⟩ := hker ⟨φx, hkerx⟩
    have hspow : φx ^ s ^ m' = 1 := by
      simpa using congrArg Subtype.val hm'
    have hcop : Nat.Coprime (t ^ m) (s ^ m') :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes ht (Fact.out (p := s.Prime))).mpr (Ne.symm hst))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one htpow) (orderOf_dvd_of_pow_eq_one hspow))
  have hconj : x * p * x⁻¹ = p := by
    have h1 := congrArg (fun σ : MulAut ↥P => ((σ ⟨p, hp⟩ : ↥P) : G)) hφx1
    simpa [hφx] using h1
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

theorem not_dvd_card_GL_le_two {s r : ℕ} [Fact s.Prime] (hr : r.Prime) (hsr : s ≠ r)
    (hrs : ¬ r ∣ s ^ 2 - 1) {n : ℕ} (hn : n ≤ 2) :
    ¬ r ∣ Nat.card (GL (Fin n) (ZMod s)) := by
  have hs : s.Prime := Fact.out
  have hrs1 : ¬ r ∣ s - 1 := by
    intro h
    apply hrs
    have hsq : s ^ 2 - 1 = (s + 1) * (s - 1) := by
      simpa using sq_tsub_sq s 1
    rw [hsq]
    exact dvd_mul_of_dvd_right h _
  have hrs' : ¬ r ∣ s := by
    intro h
    rcases (Nat.dvd_prime hs).mp h with h1 | h1
    · exact hr.ne_one h1
    · exact hsr h1.symm
  interval_cases n
  · rw [Matrix.card_GL_field]
    simpa using hr.not_dvd_one
  · rw [Matrix.card_GL_field]
    simpa [Fin.prod_univ_one, ZMod.card] using hrs1
  · rw [Matrix.card_GL_field, Fin.prod_univ_two]
    simp only [ZMod.card, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have hsq : s ^ 2 - s = s * (s - 1) := by
      rw [pow_two]
      have h1 : s * s - s = s * s - s * 1 := by rw [mul_one]
      rw [h1, ← Nat.mul_sub_left_distrib]
    rw [hsq]
    intro h
    rw [Nat.Prime.dvd_mul hr] at h
    rcases h with h | h
    · exact hrs h
    · rw [Nat.Prime.dvd_mul hr] at h
      rcases h with h | h
      · exact hrs' h
      · exact hrs1 h

omit [Finite G] in
theorem commutator_le_centralizer_of_frattini {s r n : ℕ} [Fact s.Prime] (hs2 : s ≠ 2)
    (hr : r.Prime) (hr4 : 4 < r) {P Q A : Subgroup G}
    (hQ : IsPGroup 2 Q) (hA : IsPGroup r A) (hQP : Q ≤ normalizer (P : Set G))
    (hAP : A ≤ normalizer (P : Set G)) (hAQ : A ≤ normalizer (Q : Set G))
    {D : Subgroup ↥P} [D.Characteristic] (hker : IsPGroup s (frattiniAction D).ker)
    (e : (↥D ⧸ frattini ↥D) ≃* Multiplicative (Fin n → ZMod s)) (hn2 : n ≤ 2) :
    ⁅Q, A⁆ ≤ centralizer (P : Set G) := by
  classical
  have hXQ : ⁅Q, A⁆ ≤ Q := by
    rw [Subgroup.commutator_comm Q A]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hAQ
  have hXN : ⁅Q, A⁆ ≤ normalizer (P : Set G) := hXQ.trans hQP
  set N : Subgroup G := normalizer (P : Set G) with hN
  set ψ : N →* MulAut ↥P := P.normalizerMonoidHom with hψ
  set κ : MulAut (↥D ⧸ frattini ↥D) →* GL (Fin n) (ZMod s) :=
    (elemAutEquivGL e).toMonoidHom with hκ
  set Θ : N →* GL (Fin n) (ZMod s) := κ.comp ((frattiniAction D).comp ψ) with hΘ
  set Qn : Subgroup N := Q.subgroupOf N with hQn
  set An : Subgroup N := A.subgroupOf N with hAn
  set P' : Subgroup (GL (Fin n) (ZMod s)) := Qn.map Θ with hP'
  have hQnp : IsPGroup 2 Qn := hQ.comap_subtype
  have hP'p : IsPGroup 2 P' := hQnp.map Θ
  have hAnQn : An ≤ normalizer (Qn : Set N) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
    intro x hx y hy
    have hx' : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    have hy' : (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp hy
    have hmem : ⁅(x : G), (y : G)⁆ ∈ Q :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp hAQ
        (Subgroup.commutator_mem_commutator hx' hy')
    rw [Subgroup.mem_subgroupOf]
    change N.subtype ⁅x, y⁆ ∈ Q
    rw [map_commutatorElement]
    exact hmem
  have hAnMap : An.map Θ ≤ normalizer (P' : Set (GL (Fin n) (ZMod s))) :=
    (Subgroup.map_mono hAnQn).trans (Subgroup.le_normalizer_map Θ)
  have hgen : ∀ q (hq : q ∈ Q), ∀ a (ha : a ∈ A),
      frattiniAction D (ψ ⟨⁅q, a⁆, hXN (Subgroup.commutator_mem_commutator hq ha)⟩) = 1 := by
    intro q hq a ha
    have hNmem : ⁅q, a⁆ ∈ N := hXN (Subgroup.commutator_mem_commutator hq ha)
    have hy_norm : Θ ⟨a, hAP ha⟩ ∈ normalizer (P' : Set (GL (Fin n) (ZMod s))) :=
      hAnMap (Subgroup.mem_map.mpr ⟨⟨a, hAP ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
    obtain ⟨m, hm⟩ := hA ⟨a, ha⟩
    have hyk : Θ ⟨a, hAP ha⟩ ^ r ^ m = 1 := by
      rw [← map_pow]
      have h1 : (⟨a, hAP ha⟩ : N) ^ r ^ m = 1 :=
        Subtype.ext (by simpa using congrArg (fun z : A => (z : G)) hm)
      rw [h1, map_one]
    have hcommGL := commute_of_mem_normalizer_GL hs2 hn2 hP'p hr hr4 hy_norm hyk
    have hcommut : Θ ⟨a, hAP ha⟩ * Θ ⟨q, hQP hq⟩ =
        Θ ⟨q, hQP hq⟩ * Θ ⟨a, hAP ha⟩ :=
      hcommGL _ (Subgroup.mem_map.mpr ⟨⟨q, hQP hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩)
    have hθ1 : Θ ⟨⁅q, a⁆, hNmem⟩ = 1 := by
      have heq : (⟨⁅q, a⁆, hNmem⟩ : N) =
          ⁅(⟨q, hQP hq⟩ : N), (⟨a, hAP ha⟩ : N)⁆ := by
        ext
        rfl
      rw [heq, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcommut.symm
    have hfa : κ (frattiniAction D (ψ ⟨⁅q, a⁆, hNmem⟩)) = κ 1 :=
      hθ1.trans (map_one κ).symm
    exact (elemAutEquivGL e).injective hfa
  have hXT : ⁅Q, A⁆ ≤ ((frattiniAction D).ker.comap ψ).map N.subtype := by
    rw [Subgroup.commutator_le]
    intro q hq a ha
    refine Subgroup.mem_map.mpr
      ⟨⟨⁅q, a⁆, hXN (Subgroup.commutator_mem_commutator hq ha)⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    exact hgen q hq a ha
  refine le_centralizer_of_frattiniAction_eq_one (s := s) (t := 2) Nat.prime_two hs2
    (hQ.to_le hXQ) hXN hker ?_
  intro x hx
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (hXT hx)
  have hkx' : (⟨x, hXN hx⟩ : N) = k := Subtype.ext hkx.symm
  rw [hkx']
  exact MonoidHom.mem_ker.mp (Subgroup.mem_comap.mp hk)

theorem commutator_le_centralizer_of_pRank_le_two {s r : ℕ} [Fact s.Prime] (hs2 : s ≠ 2)
    (hr : r.Prime) (hr4 : 4 < r) {P Q A : Subgroup G} (hP : IsPGroup s P)
    (hrank : CFSG.Open.pRank s P ≤ 2) (hQ : IsPGroup 2 Q) (hA : IsPGroup r A)
    (hQP : Q ≤ normalizer (P : Set G)) (hAP : A ≤ normalizer (P : Set G))
    (hAQ : A ≤ normalizer (Q : Set G)) :
    ⁅Q, A⁆ ≤ centralizer (P : Set G) := by
  classical
  rcases subsingleton_or_nontrivial ↥P with hsub | hnt
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp1 : p = 1 := congrArg Subtype.val (Subsingleton.elim ⟨p, hp⟩ ⟨1, P.one_mem⟩)
    rw [hp1, mul_one, one_mul]
  · obtain ⟨D, hDc, hDne, hDexp, hDZ, htors, hker⟩ := supercritical_witness hs2 hP
    have := hDc
    have hDp : IsPGroup s ↥D := hP.to_subgroup D
    have hcardD : Nat.card (↥D ⧸ frattini ↥D) ≤ s ^ 2 := by
      refine CFSG.RankThree.PartOne.PlaneCore.card_frattini_quotient_le
        (Fact.out (p := s.Prime)) hDp (fun x => Subtype.ext (hDexp x x.2)) ?_ ?_
      · rw [commutator_def, Subgroup.commutator_le]
        intro g₁ _ g₂ _
        rw [Subgroup.mem_center_iff]
        intro z
        have hmem : ((⁅g₁, g₂⁆ : ↥D) : ↥P) ∈ ⁅D, (⊤ : Subgroup ↥P)⁆ :=
          Subgroup.commutator_mem_commutator g₁.2 (Subgroup.mem_top _)
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hDZ hmem).2 z z.2)
      · intro E hE k hk
        have := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.le_pRank_of_elementary E hk
          (Fact.out (p := s.Prime)).one_lt
        omega
    obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
    have hWp : IsPGroup s (↥D ⧸ frattini ↥D) := fun x => ⟨1, by rw [pow_one, hWpow]⟩
    obtain ⟨n, hn⟩ := hWp.exists_card_eq
    obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hn
    have hn2 : n ≤ 2 := by
      rw [hn] at hcardD
      exact (Nat.pow_le_pow_iff_right (Fact.out (p := s.Prime)).one_lt).mp hcardD
    exact commutator_le_centralizer_of_frattini hs2 hr hr4 hQ hA hQP hAP hAQ hker e hn2

theorem le_centralizer_of_not_dvd {s r : ℕ} [Fact s.Prime] (hs2 : s ≠ 2) (hr : r.Prime)
    (hsr : s ≠ r) (hrs : ¬ r ∣ s ^ 2 - 1) {P A : Subgroup G} (hP : IsPGroup s P)
    (hrank : CFSG.Open.pRank s P ≤ 2) (hA : IsPGroup r A)
    (hAP : A ≤ normalizer (P : Set G)) : A ≤ centralizer (P : Set G) := by
  classical
  rcases subsingleton_or_nontrivial ↥P with hsub | hnt
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx1 : x = 1 := congrArg Subtype.val (Subsingleton.elim ⟨x, hx⟩ ⟨1, P.one_mem⟩)
    rw [hx1, mul_one, one_mul]
  · obtain ⟨D, hDc, hDne, hDexp, hDZ, htors, hker⟩ := supercritical_witness hs2 hP
    have := hDc
    have hDp : IsPGroup s ↥D := hP.to_subgroup D
    have hcardD : Nat.card (↥D ⧸ frattini ↥D) ≤ s ^ 2 := by
      refine CFSG.RankThree.PartOne.PlaneCore.card_frattini_quotient_le
        (Fact.out (p := s.Prime)) hDp (fun x => Subtype.ext (hDexp x x.2)) ?_ ?_
      · rw [commutator_def, Subgroup.commutator_le]
        intro g₁ _ g₂ _
        rw [Subgroup.mem_center_iff]
        intro z
        have hmem : ((⁅g₁, g₂⁆ : ↥D) : ↥P) ∈ ⁅D, (⊤ : Subgroup ↥P)⁆ :=
          Subgroup.commutator_mem_commutator g₁.2 (Subgroup.mem_top _)
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hDZ hmem).2 z z.2)
      · intro E hE k hk
        have := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.le_pRank_of_elementary E hk
          (Fact.out (p := s.Prime)).one_lt
        omega
    obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
    have hWp : IsPGroup s (↥D ⧸ frattini ↥D) := fun x => ⟨1, by rw [pow_one, hWpow]⟩
    obtain ⟨n, hn⟩ := hWp.exists_card_eq
    obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary
      hWcomm hWpow hn
    have hn2 : n ≤ 2 := by
      rw [hn] at hcardD
      exact (Nat.pow_le_pow_iff_right (Fact.out (p := s.Prime)).one_lt).mp hcardD
    have hnotdvd := not_dvd_card_GL_le_two hr hsr hrs hn2
    refine le_centralizer_of_frattiniAction_eq_one (s := s) (t := r) hr hsr hA hAP hker ?_
    intro a ha
    set φa : MulAut ↥P := P.normalizerMonoidHom ⟨a, hAP ha⟩ with hφa
    have hGL1 : elemAutEquivGL e
        (frattiniAction D φa) = 1 := by
      obtain ⟨m, hm⟩ := hA ⟨a, ha⟩
      have hGLpow : (elemAutEquivGL e
          (frattiniAction D φa)) ^ r ^ m = 1 := by
        rw [← map_pow]
        have hφpow : (frattiniAction D φa) ^ r ^ m = 1 := by
          rw [← map_pow]
          have h1 : φa ^ r ^ m = 1 := by
            rw [hφa, ← map_pow]
            have h2 : (⟨a, hAP ha⟩ : normalizer (P : Set G)) ^ r ^ m = 1 :=
              Subtype.ext (by simpa using congrArg (fun y : A => (y : G)) hm)
            rw [h2, map_one]
          rw [h1, map_one]
        rw [hφpow, map_one]
      have hcop : Nat.Coprime (r ^ m) (Nat.card (GL (Fin n) (ZMod s))) :=
        Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hr).mpr hnotdvd)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one hGLpow) (orderOf_dvd_natCard _))
    exact (elemAutEquivGL e).injective
      (hGL1.trans (map_one _).symm)

theorem pRank_le_two_of_le {N P : Subgroup G} {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hPN : P ≤ N) (h3 : CFSG.Open.pRank 3 N ≤ 1)
    (hsN : ∀ s : ℕ, s.Prime → 3 < s → CFSG.Open.pRank s N ≤ 2) :
    CFSG.Open.pRank s P ≤ 2 := by
  rcases eq_or_ne s 3 with rfl | hs3
  · exact (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hPN).trans (by omega)
  · refine (CFSG.SectionRank.pRank_mono hs.one_lt hPN).trans (hsN s hs ?_)
    have := hs.two_le
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN
