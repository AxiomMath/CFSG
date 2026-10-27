module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Vol2.Ch11SecD556B
public import CFSG.Quasithin.Vol2.Ch11SecJX

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

abbrev Ygrp (L V₁ : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (V₁ : Set G) ⊓ sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))

abbrev Cgrp (T L I V₁ : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (V₁ : Set G) ⊓
    sectionCentralizer (LOf L V₁) (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))

omit [Finite G] in
theorem Ygrp_le_G₁ : Ygrp L V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  inf_le_left.trans (Subgroup.centralizer_le_normalizer _)

namespace Core

variable (C : Core G T L I n V₁)

include C in
theorem Ygrp_le_Cgrp : Ygrp L V₁ ≤ Cgrp T L I V₁ := by
  intro y hy
  have hK := C.hK
  have hyG₁ := Ygrp_le_G₁ hy
  obtain ⟨-, hyK, hyO, hyc⟩ := hy
  rw [hK] at hyK hyO hyc
  refine ⟨hyG₁, hyK, le_normalizer_conjClosure _ _ hyG₁, fun k hk => ?_⟩
  exact C.pCoreOf_lOf_le_U (hyc k hk)

include C in
theorem x_mem_Cgrp {x : ↥L} {c : GaloisField 2 n} {hc : c ≠ 0} (hx : C.St.D.θ x = dg c hc) :
    (x : G) ∈ Cgrp T L I V₁ :=
  ⟨x_mem_G₁ hx, x_mem_normalizer_lOf hx, le_normalizer_conjClosure _ _ (x_mem_G₁ hx),
    fun _ hk => x_comm_mem_U hx hk⟩

include C in
theorem coprime_card_Ygrp (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) :
    Nat.Coprime (Nat.card ↥(Ygrp L V₁)) (2 ^ n - 1) := by
  have h := C.h
  have hV₁ := C.hV₁
  have hTG₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hV₁O : V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      (h.fsu.sylow.1.to_le ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)))
  have hO2ne : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := fun hb =>
    SecA.IsVi.ne_bot h hV₁ le_rfl (le_bot_iff.mp (hb ▸ hV₁O))
  have hH₁ : InH (LOf L V₁ ⊔ T) (Subgroup.normalizer (V₁ : Set G)) :=
    ⟨sup_le (SecD.lOf_le_normalizer L V₁) hTG₁, hO2ne⟩
  have hH₁M : ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := fun hle =>
    (h1154 G T L I n V₁ h hV₁).1 ((Subgroup.centralizer_le_normalizer _).trans hle)
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  exact (h1156 G T L I n V₁ X _ h hV₁ hX hH₁ hH₁M le_rfl).1

include C in
theorem Ygrp_le_normalizer_V
    (h2 : ∀ y ∈ Ygrp L V₁, ∃ k : ℕ, ∀ u ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)),
      y ^ (2 ^ k) * u * (y ^ (2 ^ k))⁻¹ * u⁻¹ ∈ V₁) :
    Ygrp L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  set U := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hU
  set N := sectionCentralizer U V₁ with hN
  have hYU : Ygrp L V₁ ≤ Subgroup.normalizer (U : Set G) :=
    Ygrp_le_G₁.trans (le_normalizer_conjClosure _ _)
  have hTG₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer C.hV₁
  have hsylG₁ : IsSylowTwoOf T (Subgroup.normalizer (V₁ : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo C.h.fsu.sylow hTG₁
  have hsyl : IsSylowTwoOf (T ⊓ Ygrp L V₁) (Ygrp L V₁) :=
    B6.isSylowTwoOf_inf_normal hsylG₁ Ygrp_le_G₁ (SecD.normalizer_le_normalizer_Y L V₁)
  have hYN : Ygrp L V₁ ≤ Subgroup.normalizer (N : Set G) := fun y hy =>
    SecD.mem_normalizer_sectionCentralizer (hYU hy) (Ygrp_le_G₁ hy)
  have hpow : ∀ y ∈ Ygrp L V₁, ∃ k : ℕ, y ^ (2 ^ k) ∈ N := by
    intro y hy
    obtain ⟨k, hk⟩ := h2 y hy
    exact ⟨k, Subgroup.pow_mem _ (hYU hy) _, Subgroup.pow_mem _ (Ygrp_le_G₁ hy) _, hk⟩
  have hle := F7.isSylowTwoOf_le_sup_of_two_power hsyl hYN hpow
  refine hle.trans (sup_le ?_ (inf_le_left.trans C.St.hyp.base.T_le_normV))
  intro g hg
  refine A4.mem_normalizer_of_conj_mem fun v hv => ?_
  have h1 := hg.2.2 v (le_conjClosure _ _ hv)
  have h3 := (fsuV T I).mul_mem (C.St.hyp.base.le_V h1) hv
  simpa using h3

end Core

end CFSG.Quasithin.Vol2.Ch11.SecJ
