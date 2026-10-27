module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUMono

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace SUModel

variable {f : ℕ} {K : Type} [Field K] {G : Type} [Group G] (h : UnitaryFieldData 2 f K)
  {n : ℕ} {φ : ↥(unitarySU 2 f K n) →* G}

variable {h} in
theorem SemiActs.inv {g : G} {A : GL (Fin n) K} {σ : K ≃+* K} (hg : SemiActs h φ g A σ) :
    SemiActs h φ g⁻¹ (glAut σ⁻¹ A⁻¹) σ⁻¹ := by
  refine ⟨glAut_mem_unitary h ((primeFormUnitary h _).inv_mem hg.1) σ⁻¹, fun s s' hs' => ?_⟩
  have hN : glAut σ (glAut σ⁻¹ A⁻¹) = A⁻¹ := glAut_glAut_inv σ A⁻¹
  have hS : glAut σ (glAut σ⁻¹ (s : GL (Fin n) K)) = s := glAut_glAut_inv σ (s : GL (Fin n) K)
  have h1 := hg.2 s' s (by
    rw [hs', map_mul, map_mul, map_inv (glAut σ), hN, hS]
    group)
  calc g⁻¹ * φ s * g⁻¹⁻¹ = g⁻¹ * (g * φ s' * g⁻¹) * g := by rw [h1, inv_inv]
    _ = φ s' := by group

variable {m : ℕ} {φ : ↥(unitarySU 2 f K (m + 1)) →* G}

variable {h} in
theorem SemiActs.exists_scalar (hn : 3 ≤ m + 1) (hnq : (m + 1, 2 ^ f) ≠ (3, 2)) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1))) {g : G}
    {A A' : GL (Fin (m + 1)) K} {σ : K ≃+* K} (hA : SemiActs h φ g A σ)
    (hA' : SemiActs h φ g A' σ) :
    ∃ c : Kˣ, A' = GeneralLinearGroup.scalar (Fin (m + 1)) c * A := by
  have h1 := hA'.mul hA.inv
  rw [mul_inv_cancel, glAut_glAut_inv, mul_inv_cancel] at h1
  obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn hnq hp hpq hker
    (semiActs_one_iff.mp h1).2
  exact ⟨c, by rw [← hc, inv_mul_cancel_right]⟩

theorem exists_expoU {p : ℕ} [NeZero p] {ω : Kˣ} (hω : IsPrimitiveRoot ω p) {g : G}
    (hg : g ∈ UnitModel.frameTorus p h φ) : ∃ a : Fin (m + 1) → ZMod p,
      SURep.GGFrameActs φ g (fun i => ω ^ (a i).val) := by
  obtain ⟨d, hd, hgd⟩ := hg
  choose a ha using fun i => LinModel.exists_eq_pow_val hω (hd i)
  refine ⟨a, ?_⟩
  have : (fun i => ω ^ (a i).val) = d := funext fun i => (ha i).symm
  rw [this]
  exact hgd

open Classical in
@[expose] noncomputable def expoU (p : ℕ) [NeZero p] (φ : ↥(unitarySU 2 f K (m + 1)) →* G)
    {ω : Kˣ} (hω : IsPrimitiveRoot ω p) (g : G) : Fin (m + 1) → ZMod p :=
  if hg : g ∈ UnitModel.frameTorus p h φ then (exists_expoU h hω hg).choose else 0

theorem expoU_spec {p : ℕ} [NeZero p] {ω : Kˣ} (hω : IsPrimitiveRoot ω p) {g : G}
    (hg : g ∈ UnitModel.frameTorus p h φ) :
    SURep.GGFrameActs φ g (fun i => ω ^ (expoU h p φ hω g i).val) := by
  classical
  have h1 := (exists_expoU h hω hg).choose_spec
  simp only [expoU, hg, ↓reduceDIte]
  exact h1

include h in
theorem exists_const_of_frameActs (hn : 3 ≤ m + 1) (hkerφ : SURep.GGFrameKer φ) {p : ℕ}
    [NeZero p] {ω : Kˣ} (hω : IsPrimitiveRoot ω p) {g : G} {a b : Fin (m + 1) → ZMod p}
    (ha : SURep.GGFrameActs φ g (fun i => ω ^ (a i).val))
    (hb : SURep.GGFrameActs φ g (fun i => ω ^ (b i).val)) :
    ∃ c : ZMod p, ∀ i, b i = a i + c := by
  refine ⟨b 0 - a 0, fun i => ?_⟩
  have h1 := SURep.ratio_eq_of_frameActs hkerφ h hn ha hb i 0
  apply LinModel.pow_val_injective hω
  rw [LinModel.pow_val_add hω.pow_eq_one, LinModel.pow_val_sub hω.pow_eq_one]
  have h2 : ω ^ (b i).val = ω ^ (a i).val * ω ^ (b 0).val * (ω ^ (a 0).val)⁻¹ := by
    rw [h1, mul_comm (ω ^ (a 0).val), mul_inv_cancel_right]
  rw [h2, mul_assoc]


include h in
theorem isCycle_of_isPermOf (hn : 3 ≤ m + 1) (hnq : (m + 1, 2 ^ f) ≠ (3, 2)) {p : ℕ}
    (hp : p.Prime) (hmp : m + 1 = p) (hpq : p ∣ 2 ^ f + 1)
    (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hC : Subgroup.centralizer (φ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBs : UnitModel.frameTorus p h φ = Bs) {z : G}
    (hzC : z ∉ Subgroup.centralizer (Bs : Set G)) (hzp : z ^ p = 1) {A : GL (Fin (m + 1)) K}
    (hA : (z, A) ∈ SUTorus.suPairs φ) {π : Equiv.Perm (Fin (m + 1))}
    (hπ : LinModel.IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) π) :
    π.IsCycle ∧ π.support = Finset.univ ∧ π ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hπ1 : π ≠ 1 := by
    rintro rfl
    obtain ⟨d, hd⟩ := LinModel.IsPermOf.exists_eq_diagGL hπ
    rw [hd, ← diagHom_eq_diagGL] at hA
    apply hzC
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hBs] at hb
    obtain ⟨e, -, hbe⟩ := hb
    exact commute_of_mem_suPairs_diag hC (mem_suPairs_of_frameActs h hbe) hA
  have hπp : π ^ p = 1 := by
    have h1 := (SUTorus.suPairs φ).pow_mem hA p
    rw [Prod.pow_mk, hzp] at h1
    obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn hnq hp hpq hker h1
    have h2 := hπ.pow p
    rw [← Units.val_pow_eq_pow_val, hc] at h2
    have h3 : LinModel.IsPermOf ((GeneralLinearGroup.scalar (Fin (m + 1)) c :
        GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 1 := by
      have := LinModel.IsPermOf.scalar_mul (A := (1 : GL (Fin (m + 1)) K))
        (by rw [Units.val_one]; exact LinModel.isPermOf_one) c
      rwa [mul_one] at this
    exact h2.unique h3
  have hord : orderOf π = p := orderOf_eq_prime hπp hπ1
  have hcyc : π.IsCycle := Equiv.Perm.isCycle_of_prime_order' (by rw [hord]; exact hp)
    (by rw [Fintype.card_fin, hord, hmp]; omega)
  refine ⟨hcyc, ?_, hπp⟩
  apply Finset.eq_univ_of_card
  rw [← hcyc.orderOf, hord, Fintype.card_fin, hmp]

variable (hn : 3 ≤ m + 1) (hq : ¬(m + 1 = 3 ∧ 2 ^ f = 2))
  (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
  (hC : Subgroup.centralizer (φ.range : Set G) = ⊥)

include hn hq hker hC in
theorem regularConj_injective {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) {z : G}
    {A : GL (Fin (m + 1)) K} (hAU : A ∈ primeFormUnitary h (idGram K (m + 1)))
    (hzA : (z, A) ∈ SUTorus.suPairs φ) {π : Equiv.Perm (Fin (m + 1))}
    (hπ : LinModel.IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) π) (hcyc : π.IsCycle)
    (hsupp : π.support = Finset.univ) {g : G} (hg : g ∈ Subgroup.normalizer (φ.range : Set G))
    {d : Fin (m + 1) → Kˣ} (hd : SURep.GGFrameActs φ (g⁻¹ * z * g) d) :
    Function.Injective d := by
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  obtain ⟨B, σ, hB⟩ := exists_semiActs h hn hq hker hC hg
  have e1 := (semiActs_one_iff.mpr ⟨hAU, hzA⟩).mul hB
  have e2 := hB.mul (semiActs_of_frameActs (h := h) hd)
  rw [glAut_one_apply, one_mul] at e1
  rw [mul_one, show g * (g⁻¹ * z * g) = z * g by group] at e2
  obtain ⟨c, hc⟩ := e1.exists_scalar hn hnq hp hpq hker e2
  have hAB' : A * B = B * (GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * glAut σ (diagHom (m + 1) d)) :=
    calc A * B = GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ *
          (GeneralLinearGroup.scalar (Fin (m + 1)) c * (A * B)) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      _ = GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * (B * glAut σ (diagHom (m + 1) d)) := by
          rw [hc]
      _ = B * (GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * glAut σ (diagHom (m + 1) d)) := by
          rw [← mul_assoc, (TypeA.PGLTor.commute_scalar c⁻¹ B).eq, mul_assoc]
  have hAB : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        diagonal fun i => ((c⁻¹ : Kˣ) : K) * σ ((d i : Kˣ) : K) := by
    have h1 := congrArg (fun X : GL (Fin (m + 1)) K => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
      hAB'
    simp only [Units.val_mul] at h1
    rw [h1, GeneralLinearGroup.coe_scalar, coe_glAut, coe_diagHom, diagonal_map (map_zero σ),
      scalar_apply, diagonal_mul_diagonal]
  have hinj := LinModel.injective_of_mul_eq_mul_diagonal hπ hcyc hsupp B
    (fun i => mul_ne_zero (Units.ne_zero _) ((map_ne_zero σ).mpr (Units.ne_zero _))) hAB
  intro i j hij
  apply hinj
  simp only [hij]


theorem pow_val_norm {p : ℕ} (hpq : p ∣ 2 ^ f + 1) {ω : Kˣ} (hωp : ω ^ p = 1) (k : ℕ) :
    ((ω ^ k : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul,
    pow_add_one_of_pow_eq_one hpq hωp, one_pow, Units.val_one]

include hn hq hker hC in
theorem torusCoords_of_triple {p : ℕ} (hp : p.Prime) (hmp : m + 1 = p)
    (hpq : p ∣ 2 ^ f + 1) (hkerφ : SURep.GGFrameKer φ) {ω : Kˣ} (hω : IsPrimitiveRoot ω p)
    {Bs : Subgroup G} (hBs : UnitModel.frameTorus p h φ = Bs)
    (hmat : ∀ u ∈ Subgroup.normalizer (Bs : Set G), (∃ k, u ^ (p ^ k) = 1) →
      ∃ A : GL (Fin (m + 1)) K, A ∈ primeFormUnitary h (idGram K (m + 1)) ∧
        (u, A) ∈ SUTorus.suPairs φ)
    (hmono : ∀ u ∈ Subgroup.normalizer (Bs : Set G), ∀ A : GL (Fin (m + 1)) K,
      (u, A) ∈ SUTorus.suPairs φ → ∃ π,
        LinModel.IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) π)
    (h5 : ∀ b ∈ Bs, ∀ d : Fin (m + 1) → Kˣ, SURep.GGFrameActs φ b d →
      ∀ g ∈ Subgroup.normalizer (φ.range : Set G),
        (∃ L : Subgroup G, IsComponentOf L (φ.range ⊓ Subgroup.centralizer {g * b * g⁻¹}) ∧
          GGTypeAk f L) →
        ∃ j₁ j₂ j₃ : Fin (m + 1), j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧ d j₁ = d j₂ ∧ d j₁ = d j₃)
    {z : G} (hzN : z ∈ Subgroup.normalizer (Bs : Set G))
    (hzC : z ∉ Subgroup.centralizer (Bs : Set G)) (hzp : z ^ p = 1) :
    ∃ v : G → ZMod p → ZMod p, GGTorusCoords p Bs φ.range f z v := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  obtain ⟨A, hAU, hA⟩ := hmat z hzN ⟨1, by rw [pow_one]; exact hzp⟩
  obtain ⟨π, hπ⟩ := hmono z hzN A hA
  obtain ⟨hcyc, hsupp, hπp⟩ := isCycle_of_isPermOf h hn hnq hp hmp hpq hker hC hBs hzC hzp hA hπ
  have hbij := LinModel.cycleIdx_bijective (p := p) hmp hcyc hsupp hπp
  set ι : ZMod p → Fin (m + 1) := LinModel.cycleIdx π with hιdef
  set e := expoU h p φ hω with hedef
  have hespec : ∀ g ∈ Bs, SURep.GGFrameActs φ g (fun i => ω ^ (e g i).val) := fun g hg =>
    expoU_spec h hω (by rw [hBs]; exact hg)
  refine ⟨fun g j => e g (ι j), ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a ha b hb
    have h1 := (hespec a ha).mul h (hespec b hb)
    have h2 : ((fun i => ω ^ (e a i).val) * fun i => ω ^ (e b i).val) =
        fun i => ω ^ ((e a + e b) i).val := funext fun i => by
      rw [Pi.mul_apply, Pi.add_apply, LinModel.pow_val_add hω.pow_eq_one]
    rw [h2] at h1
    obtain ⟨c, hc⟩ := exists_const_of_frameActs h hn hkerφ hω h1 (hespec _ (Bs.mul_mem ha hb))
    exact ⟨c, fun j => by
      show e (a * b) (ι j) = e a (ι j) + e b (ι j) + c
      rw [hc (ι j), Pi.add_apply]⟩
  ·
    rintro a ha ⟨c, hc⟩
    have hconst : ∀ i, e a i = c := fun i => by
      obtain ⟨j, rfl⟩ := hbij.2 i
      exact hc j
    have h1 := hespec a ha
    have h2 : (fun i => ω ^ (e a i).val) = fun i => ω ^ c.val * (1 : Fin (m + 1) → Kˣ) i :=
      funext fun i => by rw [hconst i, Pi.one_apply, mul_one]
    rw [h2] at h1
    exact UnitModel.eq_one_of_frameActs_one hC
      (UnitModel.frameActs_of_scalar h1 fun i => by rw [Pi.one_apply, Units.val_one, one_pow])
  ·
    intro a ha
    have hza : z⁻¹ * a * z ∈ Bs := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hzN) a).mp ha
      rwa [inv_inv] at this
    have h1 := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem
      ((SUTorus.suPairs φ).inv_mem hA) (mem_suPairs_of_frameActs h (hespec a ha))) hA
    rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, diagHom_eq_diagGL,
      LinModel.inv_mul_diagGL_mul hπ, ← diagHom_eq_diagGL] at h1
    have h1' : SURep.GGFrameActs φ (z⁻¹ * a * z) (fun i => ω ^ (e a (π i)).val) :=
      ⟨fun i => pow_val_norm hpq hω.pow_eq_one _, fun s s' hs' => h1.2 s s' hs'⟩
    obtain ⟨c, hc⟩ := exists_const_of_frameActs h hn hkerφ hω (a := fun i => e a (π i)) h1'
      (hespec _ hza)
    refine ⟨c, fun j => ?_⟩
    show e (z⁻¹ * a * z) (ι j) = e a (ι (j + 1)) + c
    have hc' := hc (ι j)
    rw [hc', hιdef, LinModel.cycleIdx_succ hπp]
  ·
    intro z' hz'N hz'C hz'p g hg hgz
    obtain ⟨A', hA'U, hA'⟩ := hmat z' hz'N ⟨1, by rw [pow_one]; exact hz'p⟩
    obtain ⟨π', hπ'⟩ := hmono z' hz'N A' hA'
    obtain ⟨hcyc', hsupp', -⟩ :=
      isCycle_of_isPermOf h hn hnq hp hmp hpq hker hC hBs hz'C hz'p hA' hπ'
    have hinj := regularConj_injective h hn hq hker hC hp hpq hA'U hA' hπ' hcyc' hsupp' hg
      (hespec _ hgz)
    intro j₁ j₂ hj
    apply hbij.1
    have h1 : ω ^ (e (g⁻¹ * z' * g) (ι j₁)).val = ω ^ (e (g⁻¹ * z' * g) (ι j₂)).val := by
      simp only at hj
      rw [hj]
    exact hinj h1
  ·
    rintro a ha g hg hK
    obtain ⟨j₁, j₂, j₃, h12, h13, h23, e12, e13⟩ := h5 a ha _ (hespec a ha) g hg hK
    obtain ⟨k₁, rfl⟩ := hbij.2 j₁
    obtain ⟨k₂, rfl⟩ := hbij.2 j₂
    obtain ⟨k₃, rfl⟩ := hbij.2 j₃
    exact ⟨k₁, k₂, k₃, fun h' => h12 (by rw [h']), fun h' => h13 (by rw [h']),
      fun h' => h23 (by rw [h']), LinModel.pow_val_injective hω e12,
      LinModel.pow_val_injective hω e13⟩

end SUModel

end CFSG.StandardType
