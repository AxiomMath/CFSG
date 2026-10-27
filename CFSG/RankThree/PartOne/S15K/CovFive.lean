module

public import CFSG.RankThree.PartOne.S15K.CovAt
public import CFSG.RankThree.PartOne.S15K.KF158A5
public import CFSG.RankThree.PartOne.S15K.LayerAdm

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.U5K.Pkg
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} {c : E}

theorem fiveT_comm (M : Model p E c) (x y : Fin 5) : fiveT M x y = fiveT M y x := by
  unfold fiveT
  rw [Equiv.swap_comm]

theorem swap_eq_of_fiveT_eq (M : Model p E c) {a b u v : Fin 5}
    (h : fiveT M a b = fiveT M u v) : Equiv.swap a b = Equiv.swap u v := by
  unfold fiveT at h
  exact M.ψ.symm.injective (Subtype.coe_injective h)

theorem fiveT_comm_disjoint (M : Model p E c) {x y u v : Fin 5} (hxu : x ≠ u) (hxv : x ≠ v)
    (hyu : y ≠ u) (hyv : y ≠ v) : fiveT M x y * fiveT M u v = fiveT M u v * fiveT M x y := by
  have key : ∀ x y u v : Fin 5, x ≠ u → x ≠ v → y ≠ u → y ≠ v → ∀ z : Fin 5,
      (Equiv.swap x y * Equiv.swap u v) z = (Equiv.swap u v * Equiv.swap x y) z := by decide
  unfold fiveT
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
    Equiv.ext (key x y u v hxu hxv hyu hyv)]

theorem exists_conj_fiveT (M : Model p E c) (σ : Equiv.Perm (Fin 5)) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw = ((M.ψ.symm σ : ↥(reflectionGroup p E)) : MulAut E) := by
  have hg : ((M.ψ.symm σ : ↥(reflectionGroup p E)) : MulAut E) ∈ torusWeyl E :=
    WeylIso.closure_le_weyl (M.ψ.symm σ).2
  exact WeylIso.exists_lift hg

theorem fiveT_conj (M : Model p E c) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (σ : Equiv.Perm (Fin 5))
    (hσ : conjAut E w hw = ((M.ψ.symm σ : ↥(reflectionGroup p E)) : MulAut E)) (x y : Fin 5) :
    conjAut E w hw * fiveT M x y * (conjAut E w hw)⁻¹ = fiveT M (σ x) (σ y) := by
  rw [hσ]
  unfold fiveT
  rw [Equiv.swap_apply_apply]
  simp [map_mul, map_inv]

theorem fiveT_fixes_autMoved {A : Subgroup G} {c₀ : G} {L : Subgroup G}
    (h : Sec12Hyp G p A c₀ L E) (M : Model p E c) {x y u v : Fin 5} (hxy : x ≠ y) (huv : u ≠ v)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) {m : E}
    (hm : m ∈ autMoved E (fiveT M x y)) : fiveT M u v m = m := by
  have C := reflCtx_of_hyp h
  have ht := fiveT_mem M hxy
  have hs := fiveT_mem M huv
  have hne : fiveT M u v ≠ fiveT M x y := by
    intro heq
    have h1 := swap_eq_of_fiveT_eq M heq
    have h2 := congrArg (fun σ : Equiv.Perm (Fin 5) => σ u) h1
    simp only [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hxu) (Ne.symm hyu)] at h2
    exact huv h2.symm
  exact C.fixes_moved (ReflCtx.mul_self_eq_one_of hs.1) (ReflCtx.mul_self_eq_one_of ht.1)
    (fiveT_comm_disjoint M hxu hxv hyu hyv).symm hs.1.2 ht.1.2 hne hm

theorem kZero_pair_le_zeroLayer (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hPair : KFU5PairEx)
    (hSU3 : KF158FiveS) {A : Subgroup G} {c₀ : G} {L : Subgroup G} (h15 : Sec15Hyp G p A c₀ L E)
    (hF : Sec12Facts G p A c₀ L E) (hout : Outcome152Five p E A (lieGenerated p E)) (M : Model p E c)
    {x y z : Fin 5} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) {b : G}
    (hb : b ∈ autFixedInG E (fiveT M x y) ⊓ autFixedInG E (fiveT M y z)) (hb1 : b ≠ 1) :
    kZero p E (fiveT M x y) ⊔ kZero p E (fiveT M y z) ≤ zeroLayer p E b := by
  have h := h15.h12
  obtain ⟨J, hKJ, hBJ, hJθ, S, hSJ, hS1, hS2, hSN, hSc⟩ :=
    exists_pair_J hS h82 hPair hSU3 h15 hF hout M hxy hyz hxz
  obtain ⟨-, -, -, -, -, hcardE, -, -⟩ := id hout
  have ht := fiveT_mem M hxy
  have hBcard := card_autFixedInG_five h hcardE ht
  have hDcard := card_fiveFixedInG_inf M hxy hyz hxz
  have hBE : autFixedInG E (fiveT M x y) ≤ E := Subgroup.map_subtype_le _
  have h2 := layer_ge_of_admissible hS h82 h hBE hBcard (by rw [hBJ, hDcard, hBcard]; ring)
    (by rw [hBJ]; exact hJθ) ⟨S, hSJ, hS1, hS2, hSN, hSc⟩ (by rw [hBJ]; exact hb) hb1
  exact hKJ.trans h2

theorem kZero_le_sup_of_adj {f : ℕ} (hAtt : ∀ t ∈ reflectionSet p E, KFAt p E f t) (M : Model p E c)
    {x y z : Fin 5} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    kZero p E (fiveT M x y) ≤ kZero p E (fiveT M x z) ⊔ kZero p E (fiveT M z y) := by
  obtain ⟨-, -, -, -, κ, hκN, hκK, hκt⟩ := hAtt (fiveT M z y) (fiveT_mem M hyz.symm)
  have hκ : conjAut E κ hκN = ((M.ψ.symm (Equiv.swap z y) : ↥(reflectionGroup p E)) : MulAut E) :=
    hκt
  have hconj := fiveT_conj M hκN (Equiv.swap z y) hκ x z
  rw [Equiv.swap_apply_of_ne_of_ne hxz hxy, Equiv.swap_apply_left] at hconj
  have hK : kZero p E (fiveT M x y) = conjBy κ (kZero p E (fiveT M x z)) := by
    rw [← kZero_conj p (fiveT M x z) hκN, hconj]
  intro g hg
  rw [hK] at hg
  obtain ⟨k₀, hk₀, rfl⟩ := hg
  have hκ' : κ ∈ kZero p E (fiveT M x z) ⊔ kZero p E (fiveT M z y) := Subgroup.mem_sup_right hκK
  have hk₀' : k₀ ∈ kZero p E (fiveT M x z) ⊔ kZero p E (fiveT M z y) := Subgroup.mem_sup_left hk₀
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hκ' hk₀') (Subgroup.inv_mem _ hκ')

theorem all_pairs_of_edges {Q : Fin 5 → Fin 5 → Prop} (hsymm : ∀ x y, Q x y → Q y x)
    (hstep : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → Q x z → Q z y → Q x y)
    {i j k l m : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (hcov : ∀ x : Fin 5, x = i ∨ x = j ∨ x = k ∨ x = l ∨ x = m) (bij : Q i j) (bjm : Q j m)
    (bkl : Q k l) (blm : Q l m) : ∀ x y, x ≠ y → Q x y := by
  have eim : Q i m := hstep i m j him hjm.symm hij bij bjm
  have ejl : Q j l := hstep j l m hjl hlm hjm bjm (hsymm _ _ blm)
  have ekm : Q k m := hstep k m l hkm hlm.symm hkl bkl blm
  have ejk : Q j k := hstep j k m hjk hkm hjm bjm (hsymm _ _ ekm)
  have eil : Q i l := hstep i l m hil hlm him eim (hsymm _ _ blm)
  have eik : Q i k := hstep i k m hik hkm him eim (hsymm _ _ ekm)
  intro x y hxy
  rcases hcov x with rfl | rfl | rfl | rfl | rfl <;> rcases hcov y with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | assumption
    | exact hsymm _ _ (by assumption)

theorem kf158CovAtRowFive_of_model (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hPair : KFU5PairEx)
    (hSU3 : KF158FiveS) (h156 : KF156') : KF158CovAtRowFive := by
  intro G _ _ p A c L E h15 hF hout t ht _ _ _ _ _ _ _ _ a ha
  refine Or.inr (Or.inr ⟨hout, ?_⟩)
  have h := h15.h12
  have hp := h.prime
  obtain ⟨ψ, k₀, hk, hstab⟩ := exists_psi_k h15 hF hout
  let M := mkModel h15 hF hout ψ k₀ hk hstab
  obtain ⟨f, -, hAtt, -⟩ := hPair G p A c L E h15 hF hout
  obtain ⟨i, j, hij, rfl⟩ := exists_fiveT_of_mem M ht
  obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm, hcov⟩ :
      ∃ k l m : Fin 5, i ≠ k ∧ i ≠ l ∧ i ≠ m ∧ j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m ∧
        ∀ x : Fin 5, x = i ∨ x = j ∨ x = k ∨ x = l ∨ x = m := by
    have key : ∀ i j : Fin 5, i ≠ j → ∃ k l m : Fin 5, i ≠ k ∧ i ≠ l ∧ i ≠ m ∧ j ≠ k ∧ j ≠ l ∧
        j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m ∧ ∀ x : Fin 5, x = i ∨ x = j ∨ x = k ∨ x = l ∨ x = m := by
      decide
    exact key i j hij
  obtain ⟨ã, hã, hãa, hã1⟩ := exists_mem_autMoved_of_zpowers hp ht.1.2 ha
  have ha1 : a ≠ 1 := fun h1 => hã1 (Subtype.ext (hãa.trans h1))
  have hfkl : a ∈ autFixedInG E (fiveT M k l) :=
    ⟨ã, fiveT_fixes_autMoved h M hij hkl hik hil hjk hjl hã, hãa⟩
  have hflm : a ∈ autFixedInG E (fiveT M l m) :=
    ⟨ã, fiveT_fixes_autMoved h M hij hlm hil him hjl hjm hã, hãa⟩
  have hXa : kZero p E (fiveT M k l) ⊔ kZero p E (fiveT M l m) ≤ zeroLayer p E a :=
    kZero_pair_le_zeroLayer hS h82 hPair hSU3 h15 hF hout M hkl hlm hkm ⟨hfkl, hflm⟩ ha1
  obtain ⟨w, hw, hwσ⟩ := exists_conj_fiveT M (Equiv.swap i k * Equiv.swap j l)
  have hσ : (Equiv.swap i k * Equiv.swap j l) i = k ∧ (Equiv.swap i k * Equiv.swap j l) j = l ∧
      (Equiv.swap i k * Equiv.swap j l) k = i ∧ (Equiv.swap i k * Equiv.swap j l) l = j ∧
      (Equiv.swap i k * Equiv.swap j l) m = m := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hil, Equiv.swap_apply_left]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hil.symm hkl.symm]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hjk.symm hkl, Equiv.swap_apply_right]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hij.symm hjk]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hjm.symm hlm.symm,
        Equiv.swap_apply_of_ne_of_ne him.symm hkm.symm]
  have hc_ij := fiveT_conj M hw _ hwσ i j
  rw [hσ.1, hσ.2.1] at hc_ij
  have hc_kl := fiveT_conj M hw _ hwσ k l
  rw [hσ.2.2.1, hσ.2.2.2.1] at hc_kl
  have hc_lm := fiveT_conj M hw _ hwσ l m
  rw [hσ.2.2.2.1, hσ.2.2.2.2] at hc_lm
  have hwa : w * a * w⁻¹ ∈ zeroLayer p E a := by
    have h1 : a ∈ autMovedInG E (fiveT M i j) := ha ▸ Subgroup.mem_zpowers a
    have h2 : w * a * w⁻¹ ∈ conjBy w (autMovedInG E (fiveT M i j)) := Subgroup.mem_map_of_mem _ h1
    rw [← Equivariance.autMovedInG_conj (fiveT M i j) hw, hc_ij] at h2
    exact hXa ((le_sup_left : kZero p E (fiveT M k l) ≤ _)
      ((hAtt (fiveT M k l) (fiveT_mem M hkl)).2.2.2.1 h2))
  refine ⟨w, hw, hwa, ?_⟩
  have hwN : w ∈ Subgroup.normalizer (lieGenerated p E : Set G) :=
    torusNormalizer_le_lieNormalizer hp E hw
  have hXaI : zeroLayer p E a ≤ lieGenerated p E :=
    Sec158.zeroLayer_le_lieGenerated h156 h15 hF (Or.inr (Or.inr (Or.inr (Or.inr hout)))) a
  set Y := zeroLayer p E a ⊔ conjBy w (zeroLayer p E a) with hY
  apply le_antisymm
  · refine sup_le hXaI ?_
    calc conjBy w (zeroLayer p E a) ≤ conjBy w (lieGenerated p E) := Subgroup.map_mono hXaI
      _ = lieGenerated p E := lieGenerated_conjBy hp hw
  · have hXaY : zeroLayer p E a ≤ Y := le_sup_left
    have hXawY : conjBy w (zeroLayer p E a) ≤ Y := le_sup_right
    have hsymm : ∀ x y : Fin 5, kZero p E (fiveT M x y) = kZero p E (fiveT M y x) := fun x y => by
      rw [fiveT_comm]
    have b_kl : kZero p E (fiveT M k l) ≤ Y := (le_sup_left.trans hXa).trans hXaY
    have b_lm : kZero p E (fiveT M l m) ≤ Y := (le_sup_right.trans hXa).trans hXaY
    have b_ij : kZero p E (fiveT M i j) ≤ Y := by
      have : kZero p E (fiveT M i j) = conjBy w (kZero p E (fiveT M k l)) := by
        rw [← kZero_conj p (fiveT M k l) hw, hc_kl]
      rw [this]
      exact (Subgroup.map_mono (le_sup_left.trans hXa)).trans hXawY
    have b_jm : kZero p E (fiveT M j m) ≤ Y := by
      have : kZero p E (fiveT M j m) = conjBy w (kZero p E (fiveT M l m)) := by
        rw [← kZero_conj p (fiveT M l m) hw, hc_lm]
      rw [this]
      exact (Subgroup.map_mono (le_sup_right.trans hXa)).trans hXawY
    have hP := all_pairs_of_edges (Q := fun x y => kZero p E (fiveT M x y) ≤ Y)
      (fun x y hxy => by
        show kZero p E (fiveT M y x) ≤ Y
        rw [hsymm y x]
        exact hxy)
      (fun x y z hxy hyz hxz h1 h2 => (kZero_le_sup_of_adj hAtt M hxy hyz hxz).trans (sup_le h1 h2))
      hij hik hil him hjk hjl hjm hkl hkm hlm hcov b_ij b_jm b_kl b_lm
    refine sSup_le ?_
    rintro K ⟨t'', ht'', hK⟩
    obtain ⟨x, y, hxy, rfl⟩ := exists_fiveT_of_mem M ht''
    have hKeq : K = kZero p E (fiveT M x y) := hK.2 (hAtt _ ht'').1
    rw [hKeq]
    exact hP x y hxy

end CFSG.RankThree.PartOne.S15K
