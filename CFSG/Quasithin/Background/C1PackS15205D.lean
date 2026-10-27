module

public import CFSG.Quasithin.Background.C1PackS15205A
public import CFSG.Quasithin.EmptyFaithful.S14116

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

section General

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_eq_three_of_index_three {M K H T : Subgroup G} (hidx : K.relIndex M = 3)
    (hTK : T ≤ K) (hTM : ¬ 2 ∣ T.relIndex M) (hTH : T ≤ H) (hHM : H ≤ M) (hHK : ¬ H ≤ K) :
    K.relIndex H = 3 := by
  have h3ne : K.relIndex M ≠ 0 := by omega
  have hle : K.relIndex H ≤ K.relIndex M := Subgroup.relIndex_le_of_le_right hHM h3ne
  have hne1 : K.relIndex H ≠ 1 := fun h => hHK (Subgroup.relIndex_eq_one.mp h)
  have hdvd : K.relIndex H ∣ T.relIndex H := Subgroup.relIndex_dvd_of_le_left H hTK
  have hTHM : T.relIndex H * H.relIndex M = T.relIndex M :=
    Subgroup.relIndex_mul_relIndex T H M hTH hHM
  have hodd : ¬ 2 ∣ K.relIndex H := by
    intro h2
    apply hTM
    rw [← hTHM]
    exact (h2.trans hdvd).mul_right _
  omega

theorem exists_mul_of_index_three {M K H T : Subgroup G} (hidx : K.relIndex M = 3)
    (hTK : T ≤ K) (hTM : ¬ 2 ∣ T.relIndex M) (hTH : T ≤ H) (hHM : H ≤ M) (hHK : ¬ H ≤ K) :
    ∀ m ∈ M, ∃ h ∈ H, ∃ k ∈ K, m = h * k := by
  have h3 : K.relIndex H = 3 := relIndex_eq_three_of_index_three hidx hTK hTM hTH hHM hHK
  have hcard : Nat.card (M ⧸ K.subgroupOf M) ≤ Nat.card (H ⧸ K.subgroupOf H) := by
    have e1 : Nat.card (H ⧸ K.subgroupOf H) = K.relIndex H := rfl
    have e2 : Nat.card (M ⧸ K.subgroupOf M) = K.relIndex M := rfl
    rw [e1, e2, h3, hidx]
  have hbij :=
    (Subgroup.quotientSubgroupOfEmbeddingOfLE K hHM).injective.bijective_of_nat_card_le hcard
  intro m hm
  obtain ⟨q, hq⟩ := hbij.2 (QuotientGroup.mk ⟨m, hm⟩)
  obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : (QuotientGroup.mk (⟨h, hHM hh⟩ : M) : M ⧸ K.subgroupOf M) =
      QuotientGroup.mk ⟨m, hm⟩ := hq
  rw [QuotientGroup.eq] at h1
  have h2 : h⁻¹ * m ∈ K := h1
  exact ⟨h, hh, h⁻¹ * m, h2, by group⟩

omit [Finite G] in
theorem conj_mem_sup_of_commutator {A B : Subgroup G} {c : G} (hA : ∀ a ∈ A, c * a * c⁻¹ ∈ A)
    (hB : ∀ b ∈ B, c * b * c⁻¹ * b⁻¹ ∈ A) : ∀ z ∈ A ⊔ B, c * z * c⁻¹ ∈ A ⊔ B := by
  intro z hz
  rw [Subgroup.sup_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact Subgroup.mem_sup_left (hA z hz)
    · have e : c * z * c⁻¹ = (c * z * c⁻¹ * z⁻¹) * z := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hB z hz)) (Subgroup.mem_sup_right hz)
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
    rw [e]
    exact (A ⊔ B).mul_mem iha ihb
  | inv a _ ih =>
    have e : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
    rw [e]
    exact (A ⊔ B).inv_mem ih

omit [Finite G] in
theorem commutator_mem_centralizer_sup {M U W : Subgroup G}
    (hU : M ≤ Subgroup.normalizer (U : Set G)) (hW : M ≤ Subgroup.normalizer (W : Set G)) {r c : G}
    (hrM : r ∈ M) (hcM : c ∈ M) (hr : r ∈ Subgroup.centralizer (U : Set G))
    (hc : c ∈ Subgroup.centralizer (W : Set G)) :
    c * r * c⁻¹ * r⁻¹ ∈ Subgroup.centralizer ((U ⊔ W : Subgroup G) : Set G) := by
  set x : G := c * r * c⁻¹ * r⁻¹ with hx
  have hsub : U ⊔ W ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun u hu => ?_) (fun w hw => ?_)
    ·
      have hu' : c⁻¹ * u * c ∈ U := (Subgroup.mem_normalizer_iff''.mp (hU hcM) u).mp hu
      have h1 : u * r = r * u := Subgroup.mem_centralizer_iff.mp hr u hu
      have h2 : (c⁻¹ * u * c) * r = r * (c⁻¹ * u * c) := Subgroup.mem_centralizer_iff.mp hr _ hu'
      have e1 : r⁻¹ * u * r = u := by
        calc r⁻¹ * u * r = r⁻¹ * (u * r) := by group
          _ = r⁻¹ * (r * u) := by rw [h1]
          _ = u := by group
      have e2 : r * (c⁻¹ * u * c) * r⁻¹ = c⁻¹ * u * c := by
        calc r * (c⁻¹ * u * c) * r⁻¹ = (r * (c⁻¹ * u * c)) * r⁻¹ := rfl
          _ = ((c⁻¹ * u * c) * r) * r⁻¹ := by rw [h2]
          _ = c⁻¹ * u * c := by group
      have e3 : x * u * x⁻¹ = u := by
        calc x * u * x⁻¹ = c * r * c⁻¹ * (r⁻¹ * u * r) * c * r⁻¹ * c⁻¹ := by rw [hx]; group
          _ = c * (r * (c⁻¹ * u * c) * r⁻¹) * c⁻¹ := by rw [e1]; group
          _ = u := by rw [e2]; group
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp e3).symm
    ·
      have hw' : r⁻¹ * w * r ∈ W := (Subgroup.mem_normalizer_iff''.mp (hW hrM) w).mp hw
      have h1 : w * c = c * w := Subgroup.mem_centralizer_iff.mp hc w hw
      have h2 : (r⁻¹ * w * r) * c = c * (r⁻¹ * w * r) := Subgroup.mem_centralizer_iff.mp hc _ hw'
      have e1 : c⁻¹ * (r⁻¹ * w * r) * c = r⁻¹ * w * r := by
        calc c⁻¹ * (r⁻¹ * w * r) * c = c⁻¹ * ((r⁻¹ * w * r) * c) := by group
          _ = c⁻¹ * (c * (r⁻¹ * w * r)) := by rw [h2]
          _ = r⁻¹ * w * r := by group
      have e2 : c * w * c⁻¹ = w := by
        calc c * w * c⁻¹ = (w * c) * c⁻¹ := by rw [← h1]
          _ = w := by group
      have e3 : x * w * x⁻¹ = w := by
        calc x * w * x⁻¹ = c * r * (c⁻¹ * (r⁻¹ * w * r) * c) * r⁻¹ * c⁻¹ := by rw [hx]; group
          _ = c * (r * (r⁻¹ * w * r) * r⁻¹) * c⁻¹ := by rw [e1]; group
          _ = c * w * c⁻¹ := by group
          _ = w := e2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp e3).symm
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.mp (hsub hv)

end General

section Concrete

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

omit [Finite G] in
theorem le_centralizer_of_autOn_eq_bot {X V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (h : autOn X V = ⊥) : X ≤ Subgroup.centralizer (V : Set G) := fun x hx => by
  have hmem : conjAct V ⟨x, hX hx⟩ ∈ autOn X V := mem_autOn_iff_exists.mpr ⟨x, hX hx, hx, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact A4.conjAct_eq_one_iff.mp hmem

theorem Ctr5.hyp_VZ (c : Ctr5 T Mc M M₁) : Hyp14117 T Mc M M₁ (VZ T M) where
  inM := c.std.data.inM
  twoReduced := (isTwoReducedIn_VZ c.qtfe c.std.data.inM).1
  ne_bot := VZ_ne_bot c.qtfe.omegaOneCenter_ne_bot
  inM₁ := c.inM₁
  ne := c.ne
  cases := Or.inl ⟨c.ordLE, rfl⟩

theorem Ctr5.pCoreOf_H_ne_bot (c : Ctr5 T Mc M M₁) : pCoreOf 2 (M₁ ⊓ M) ≠ ⊥ := by
  intro h
  have h1 := c.hyp_VZ.pCoreOf_le_pCoreOf_inf c.qtfe
  rw [h, le_bot_iff] at h1
  exact pCoreOf_ne_bot_of_isTwoLocal c.std.data.inM.1.1 h1

theorem Ctr5.Rbar_ne_bot (h113 : StageLemma14113) (c : Ctr5 T Mc M M₁) :
    autOn (pCoreOf 2 (M₁ ⊓ M)) (V154 T Mc M) ≠ ⊥ := by
  classical
  intro hR1
  have hd := c.std.data
  have h1 := lemma_14_1_17_one h113 c.qtfe c.hyp_VZ
  by_cases hSix : Case1512Six T Mc M
  swap
  · exact h1 (by rw [← V154_eq_VZ hSix]; exact hR1)
  have hVu : V154 T Mc M = uJ154 T M := V154_eq_uJ hSix
  obtain ⟨-, hUW, hsup, -, hWne, -, hprod, hidx⟩ := id hSix
  set R : Subgroup G := pCoreOf 2 (M₁ ⊓ M) with hRdef
  have hRM : R ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hMU : M ≤ Subgroup.normalizer (uJ154 T M : Set G) := hVu ▸ hd.hMV
  have hRCU : R ≤ Subgroup.centralizer (uJ154 T M : Set G) :=
    le_centralizer_of_autOn_eq_bot (hRM.trans hMU) (by rw [← hVu]; exact hR1)
  have hMVZ : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have hMJ : M ≤ Subgroup.normalizer (mJ154 T M : Set G) :=
    le_normalizer_preOn hMVZ fun _ hg _ hy => JhatOn_normalized hg hy
  have hMW : M ≤ Subgroup.normalizer (cJ154 T M : Set G) := by
    intro g hg
    have h1 : g ∈ Subgroup.normalizer (VZ T M : Set G) := hMVZ hg
    have h2 : g ∈ Subgroup.normalizer (Subgroup.centralizer (mJ154 T M : Set G) : Set G) :=
      A4.mem_normalizer_centralizer (hMJ hg)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  have hTH : T ≤ M₁ ⊓ M := c.T_le_H
  have hTM : IsSylowTwoOf T M := isSylowTwoOf_of_le151 c.qtfe.sylow c.T_le_M
  have hfac : ∀ m ∈ M, ∃ h ∈ M₁ ⊓ M, ∃ k ∈ M ⊓ Mc, m = h * k :=
    exists_mul_of_index_three hidx (le_inf c.T_le_M c.qtfe.t_le_mc) hTM.2.2 hTH inf_le_right
      (fun hHK => c.not_H_le_Mc (hHK.trans inf_le_right))
  have hMfac : ∀ m ∈ M, ∃ c₁ ∈ M ⊓ Subgroup.centralizer (uJ154 T M : Set G),
      ∃ c₂ ∈ M ⊓ Subgroup.centralizer (cJ154 T M : Set G), ∃ h ∈ M₁ ⊓ M, m = c₁ * c₂ * h := by
    intro m hm
    obtain ⟨h, hh, k, hk, hmk⟩ := hfac m⁻¹ (M.inv_mem hm)
    have hk' : k⁻¹ ∈ ((M ⊓ Mc : Subgroup G) : Set G) := (M ⊓ Mc).inv_mem hk
    rw [← hprod] at hk'
    obtain ⟨y, hy, t, ht, hkt⟩ := Set.mem_mul.mp hk'
    obtain ⟨c₁, hc₁, c₂, hc₂, hyc⟩ := Set.mem_mul.mp hy
    refine ⟨c₁, hc₁, c₂, hc₂, t * h⁻¹, (M₁ ⊓ M).mul_mem (hTH ht) ((M₁ ⊓ M).inv_mem hh), ?_⟩
    calc m = (h * k)⁻¹ := by rw [← hmk]; group
      _ = k⁻¹ * h⁻¹ := by group
      _ = y * t * h⁻¹ := by rw [hkt]
      _ = c₁ * c₂ * (t * h⁻¹) := by rw [← hyc]; group
  have hR5 := (lemma_14_1_17_five c.qtfe c.hyp_VZ).1
  set K : Subgroup G := (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ R with hKdef
  have hconj : ∀ x ∈ M ⊓ Subgroup.centralizer (cJ154 T M : Set G), ∀ z ∈ K, x * z * x⁻¹ ∈ K := by
    intro x hx
    refine conj_mem_sup_of_commutator (fun a ha => ?_) (fun b hb => ?_)
    · refine ⟨M.mul_mem (M.mul_mem hx.1 ha.1) (M.inv_mem hx.1), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_centralizer (hMVZ hx.1)) a).mp ha.2
    · refine ⟨M.mul_mem (M.mul_mem (M.mul_mem hx.1 (hRM hb)) (M.inv_mem hx.1)) (M.inv_mem (hRM hb)),
        ?_⟩
      have := commutator_mem_centralizer_sup hMU hMW (hRM hb) hx.1 (hRCU hb) hx.2
      rwa [hsup] at this
  have hNR : ∀ x ∈ M ⊓ Subgroup.centralizer (cJ154 T M : Set G),
      x ∈ Subgroup.normalizer (R : Set G) := by
    intro x hx
    have hNK : x ∈ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨hconj x hx z, fun hz => ?_⟩
      have hx' : x⁻¹ ∈ M ⊓ Subgroup.centralizer (cJ154 T M : Set G) :=
        (M ⊓ Subgroup.centralizer (cJ154 T M : Set G)).inv_mem hx
      have := hconj x⁻¹ hx' _ hz
      simpa [mul_assoc] using this
    have := normalizer_le_normalizer_pCoreOf (r := 2) K hNK
    rwa [← hR5] at this
  have hHN : M₁ ⊓ M ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 (M₁ ⊓ M)
  have hXsub : (m0Of T Mc M : Set G) ⊆ ((M ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) *
      ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) := by
    intro m hm
    have hmM : m ∈ M := (S152Y.m0Of_le T Mc M) hm
    obtain ⟨c₁, hc₁, c₂, hc₂, h, hh, hmeq⟩ := hMfac m⁻¹ (M.inv_mem hmM)
    have hm' : m = h⁻¹ * c₂⁻¹ * c₁⁻¹ := by
      calc m = (m⁻¹)⁻¹ := by group
        _ = (c₁ * c₂ * h)⁻¹ := by rw [hmeq]
        _ = h⁻¹ * c₂⁻¹ * c₁⁻¹ := by group
    refine Set.mem_mul.mpr ⟨h⁻¹ * c₂⁻¹, ⟨M.mul_mem (M.inv_mem (hh.2)) (M.inv_mem hc₂.1), ?_⟩,
      c₁⁻¹, ⟨M.inv_mem hc₁.1, ?_⟩, hm'.symm⟩
    · exact (Subgroup.normalizer (R : Set G)).mul_mem ((Subgroup.normalizer (R : Set G)).inv_mem
        (hHN hh)) ((Subgroup.normalizer (R : Set G)).inv_mem (hNR c₂ hc₂))
    · rw [hVu]
      exact (Subgroup.centralizer (uJ154 T M : Set G)).inv_mem hc₁.2
  have hUniq : IsUniqueM (M ⊓ Subgroup.normalizer (R : Set G)) M :=
    c.std.c1522 _ (le_inf c.T_le_M (hTH.trans hHN)) inf_le_left (Or.inl hXsub)
  have hCGS : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ M := by
    intro C hCR hC1 hchar
    have hCp : IsPGroup 2 C := (pCoreOf_isPGroup 2 _).to_le hCR
    obtain ⟨M'', hM'', hle⟩ := exists_maxTwoLocal_ge
      (L := Subgroup.normalizer (C : Set G)) ⟨C, hC1, hCp, rfl⟩
    have hXle : M ⊓ Subgroup.normalizer (R : Set G) ≤ M'' :=
      (inf_le_right.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hCR hchar)).trans hle
    have hMM : M'' = M := hUniq.2 M'' ⟨hM'', hXle⟩
    rw [hMM] at hle
    exact hle
  have hcgs : cgsIn M₁ R = M₁ ⊓ M := by
    refine le_antisymm (iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hchar =>
      inf_le_inf_left M₁ (hCGS C hCR hC1 hchar)) ?_
    have hchar : (R.subgroupOf R).Characteristic := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    exact le_iSup_of_le R (le_iSup_of_le le_rfl (le_iSup_of_le c.pCoreOf_H_ne_bot
      (le_iSup_of_le hchar (le_inf inf_le_left hHN))))
  have hU16 := lemma_14_1_16 h113 c.qtfe c.inM₁ hTH inf_le_left c.pCoreOf_H_ne_bot hcgs
  exact c.ne (hU16.2 M ⟨hd.inM.1, inf_le_right⟩).symm

end Concrete

end C1Pack5

end CFSG.Quasithin
