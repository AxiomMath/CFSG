module

public import CFSG.Quasithin.H13.L32AM50b
public import CFSG.Quasithin.Background.SmithB45Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7B

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.B45Alt7 CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3
open Equiv Equiv.Perm
open scoped IsMulCommutative

section Classify

variable {M : Type} [CommGroup M] [Finite M] [Module (ZMod 2) (Additive M)]
  {Λ : Subgroup (MulAut M)} (ι : ↥Λ ≃* A7)

theorem classify_or_card16 (hirr : ∀ J : Subgroup M, (∀ l ∈ Λ, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hfix : fixV Λ = ⊥) (hcard : Nat.card M ≤ 2 ^ 12) :
    (∃ β : M ≃* ↥(G6.coreMod 7), ∀ (γ : A7) (s : M),
      (β ((ι.symm γ : MulAut M) s) : G6.PermMod 7) = G6.permAct 7 (γ : Perm (Fin 7)) (β s)) ∨
    Nat.card M = 16 := by
  classical
  have h16 : ∀ Ψ : Vec 4 ≃ₗ[ZMod 2] Additive M, Nat.card M = 16 := fun Ψ => by
    have h1 := Nat.card_congr Ψ.toEquiv
    have h2 : Nat.card (Additive M) = Nat.card M := rfl
    rw [h2] at h1
    rw [← h1, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4),
      Fintype.card_fin]
    norm_num
  have hfour : ∀ {i r : ℕ}, (i, r) ∈ [(5, 0), (8, 0), (6, 2), (10, 2)] → ∀ c : Bool, rB c = r →
      ∀ {ψ : Vec 4 →ₗ[ZMod 2] Additive M}, Function.Injective ψ →
      (∀ b s, ψ (lin 4 (blkOf i b) s) = sigma6 ι (gen b) (ψ s)) → Nat.card M = 16 := by
    intro i r h c hrc ψ hψi hψ
    have hψ' : ∀ b s, (ψ.comp (lin 4 (indQ i))) (lin 4 (blkOf (rB c) b) s) =
        sigma6 ι (gen b) ((ψ.comp (lin 4 (indQ i))) s) := by
      intro b s
      simp only [LinearMap.comp_apply]
      rw [hrc, ← lin_conj h, hψ]
    have hinj : Function.Injective (ψ.comp (lin 4 (indQ i))) := by
      intro s s' hs
      have h1 := hψi hs
      have h2 := congrArg (lin 4 (indP i)) h1
      rwa [lin_PQ h, lin_PQ h] at h2
    obtain ⟨-, -, Ψ, -⟩ := exists_four_block ι hirr hcard c hinj hψ'
    exact h16 Ψ
  have hne : (⊤ : Submodule (ZMod 2) (Additive M)) ≠ ⊥ := by
    intro h
    have hall : ∀ v : M, v = 1 := fun v => by
      have : Additive.ofMul v ∈ (⊤ : Submodule (ZMod 2) (Additive M)) := trivial
      rw [h, Submodule.mem_bot] at this
      exact this
    have h1 : ((ι.symm (gen7 false) : ↥Λ) : MulAut M) = 1 :=
      MulEquiv.ext fun v => (hall _).trans (hall v).symm
    have h2 : ι.symm (gen7 false) = 1 := Subtype.ext h1
    have h3 : gen7 false = 1 := by
      have := congrArg ι h2
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact absurd h3 (by decide)
  obtain ⟨i, hi, ψ, hψi, hψ⟩ := exists_block_emb (sigma6 ι) hne
  have hone : ∀ (hi1 : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 9),
      (∃ β : M ≃* ↥(G6.coreMod 7), ∀ (γ : A7) (s : M),
        (β ((ι.symm γ : MulAut M) s) : G6.PermMod 7) =
          G6.permAct 7 (γ : Perm (Fin 7)) (β s)) := by
    intro hi1
    have hd : eNs.getD (i + 1) 0 - eNs.getD i 0 = 1 := by
      rcases hi1 with rfl | rfl | rfl | rfl | rfl <;> decide
    set e0 : Vec (eNs.getD (i + 1) 0 - eNs.getD i 0) := Pi.single ⟨0, by omega⟩ 1 with he0
    have hv0 : ψ e0 ≠ 0 := by
      intro h
      have h1 : e0 = 0 := hψi (h.trans (map_zero ψ).symm)
      have h2 := congrFun h1 ⟨0, by omega⟩
      simp [he0] at h2
    refine exists_coreEquiv ι hirr hfix hv0 fun b => ?_
    have := hψ b e0
    rw [blkOf_one hi1, lin_one hd] at this
    exact this.symm
  interval_cases i
  · obtain ⟨-, -, Ψ, -⟩ := exists_four_block ι hirr hcard false hψi hψ
    exact Or.inr (h16 Ψ)
  · exact Or.inl (hone (by omega))
  · obtain ⟨-, -, Ψ, -⟩ := exists_four_block ι hirr hcard true hψi hψ
    exact Or.inr (h16 Ψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inl (hone (by omega))
  · exact Or.inr (hfour (r := 0) (by simp) false (by decide) hψi hψ)
  · exact Or.inr (hfour (r := 2) (by simp) true (by decide) hψi hψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inr (hfour (r := 0) (by simp) false (by decide) hψi hψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inr (hfour (r := 2) (by simp) true (by decide) hψi hψ)
  · exfalso
    have h1 : Nat.card (Vec (eNs.getD (11 + 1) 0 - eNs.getD 11 0)) ≤ Nat.card (Additive M) :=
      Nat.card_le_card_of_injective ψ hψi
    have h16' : eNs.getD (11 + 1) 0 - eNs.getD 11 0 = 16 := by decide
    rw [h16', Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 16),
      Fintype.card_fin] at h1
    have h2 : Nat.card (Additive M) = Nat.card M := rfl
    rw [h2] at h1
    have := h1.trans hcard
    norm_num at this

end Classify

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top50

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 7)} (C : Top50 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]
include C

@[expose] def IrrK : Prop :=
  ∀ J : Subgroup (Hat V H W), (∀ l ∈ C.autK, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤

@[expose] noncomputable def autE (B : Subgroup G) : Subgroup (MulAut (Hat V H W)) :=
  (B.subgroupOf H).map C.act

theorem mem_pCoreOf_iff_comm {f : G} (hf : f ∈ H) :
    f ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure V H, f * u * f⁻¹ * u⁻¹ ∈ W := by
  rw [← C.act_eq_one_iff_comm ⟨f, hf⟩, C.act_eq_one_iff, C.pi_eq_one_iff]

theorem card_autE {B : Subgroup G} (hBH : B ≤ H) :
    Nat.card (C.autE B) = (B ⊓ pCoreOf 2 H).relIndex B := by
  have hE : C.autE B = autSec (autOn B (conjClosure V H)) ⊤
      (W.subgroupOf (conjClosure V H)) := by
    ext ψ
    rw [A6.A6Mod.mem_autSec_iff (le_normalizer_conjClosure V H) C.hHUW hBH]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, Subgroup.mem_subgroupOf.mp hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  rw [hE]
  exact A6.A6Mod.card_autSec_eq (le_normalizer_conjClosure V H) C.hHUW hBH
    fun f hf => C.mem_pCoreOf_iff_comm (hBH hf)

theorem isA2_autE {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) :
    IsA2 C.act.range (C.autE B) := by
  obtain ⟨hBH, hBe, hBQ, -, -⟩ := hB
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp hBQ
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨C.act ⟨b, hBH hb⟩, ⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩, ?_⟩
    intro h1
    apply hbQ
    have h2 : C.act ⟨b, hBH hb⟩ = 1 := congrArg Subtype.val h1
    rw [C.act_eq_one_iff, C.pi_eq_one_iff] at h2
    exact h2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have := hBe.1
    have h1 : (x : G) * y = y * x := congrArg Subtype.val
      (mul_comm (⟨x, Subgroup.mem_subgroupOf.mp hx⟩ : ↥B) ⟨y, Subgroup.mem_subgroupOf.mp hy⟩)
    exact Subtype.ext h1
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h2 : x ^ 2 = 1 := Subtype.ext (hBe.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [h2, map_one]

theorem index_fixV_autE_le {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) :
    (fixV (C.autE B)).index ≤ Nat.card (C.autE B) ^ 2 := by
  obtain ⟨hBH, -, -, -, hidx⟩ := hB
  set U := conjClosure V H with hU
  set q := InternalSec.secMk (W.subgroupOf U) with hq
  set Z := (centralizerMod (fsuV1 T V) U B).subgroupOf U with hZ
  have hZf : Z.map q ≤ fixV (C.autE B) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨f, hf, rfl⟩
    have hz' : (z : G) ∈ centralizerMod (fsuV1 T V) U B := hz
    have hf' : (f : G) ∈ B := hf
    have hc := (mem_centralizerMod.mp hz').2.2 (f : G) hf'
    rw [C.act_secMk]
    have h1 : (f : G) * z * (f : G)⁻¹ * (z : G)⁻¹ ∈ W := by
      apply C.hV₁W
      have := inv_mem hc
      rwa [show ((z : G) * f * (z : G)⁻¹ * (f : G)⁻¹)⁻¹ = (f : G) * z * (f : G)⁻¹ * (z : G)⁻¹ by
        group] at this
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    exact h1
  have hpos : ∀ X : Subgroup (Hat V H W), 0 < X.index := fun X =>
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hposU : 0 < Z.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : (fixV (C.autE B)).index ≤ (Z.map q).index :=
    Nat.le_of_dvd (hpos _) (Subgroup.index_dvd_of_le hZf)
  have h2 : (Z.map q).index ≤ Z.index :=
    Nat.le_of_dvd hposU (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
  calc (fixV (C.autE B)).index ≤ Z.index := h1.trans h2
    _ = (centralizerMod (fsuV1 T V) U B).relIndex U := rfl
    _ ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := hidx
    _ = Nat.card (C.autE B) ^ 2 := by rw [C.card_autE hBH]

theorem sq_eq_one (v : Hat V H W) : v ^ 2 = 1 := by
  rw [pow_two]
  exact C.sec_sq v

theorem irrK_cases (hirr : C.IrrK) {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) :
    (∃ β : Hat V H W ≃* ↥(G6.coreMod 7), ∀ (γ : A7) (s : Hat V H W),
      (β ((C.iota.symm γ : MulAut (Hat V H W)) s) : G6.PermMod 7) =
        G6.permAct 7 (γ : Perm (Fin 7)) (β s)) ∨
    (Nat.card (Hat V H W) = 16 ∧ C.act.range = C.autK) := by
  have hirrS : XMod.IsIrrSec ↥C.autK (⊥ : Subgroup (Hat V H W)) ⊤ := by
    refine ⟨bot_lt_iff_ne_bot.mpr C.top_ne_bot, fun J hJ _ _ => hirr J fun l hl v hv => ?_⟩
    exact hJ ⟨l, hl⟩ v hv
  have hcard := B45Alt7.card_le_of_cubic C.ctx hirrS C.iota C.emb C.emb_injective
    (fun l => C.emb_eq_iota l) (C.isA2_autE hB) (C.index_fixV_autE_le hB)
  let _ : Module (ZMod 2) (Additive (Hat V H W)) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul]
      exact C.sq_eq_one _
    exact toMul_eq_one.1 h3
  rcases classify_or_card16 C.iota hirr C.fixV_eq_bot hcard with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    have hL : Nat.card C.autK = 2520 := by
      rw [Nat.card_congr C.iota.toEquiv]
      exact Alt7.card_alt7
    have hnorm := L246.C123.normalizer_eq_of_card_2520 C.sq_eq_one h hL
    refine le_antisymm (fun g hg => ?_) C.autK_le
    have hg' : g ∈ Subgroup.normalizer (C.autK : Set (MulAut (Hat V H W))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro l
      refine ⟨fun hl => C.autK_normal g hg l hl, fun hl => ?_⟩
      have := C.autK_normal g⁻¹ (inv_mem hg) _ hl
      simpa [mul_assoc] using this
    rw [hnorm] at hg'
    exact hg'

end Top50

end CFSG.Quasithin.H13.L32A.C
