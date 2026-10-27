module

public import CFSG.Quasithin.EmptyFaithful.S153E56P11
public import CFSG.Quasithin.EmptyFaithful.S153E56P12

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section D8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

@[expose] noncomputable def AxQ : Subgroup (Ut T M V₁ Mc) where
  carrier := {c | c ∈ Et2 T M V₁ Mc y t₁ ∧ bet S.cx c (aa S) = 0}
  one_mem' := ⟨Subgroup.one_mem _, (split_model S).one_left _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha0⟩ ⟨hb, hb0⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    rw [bet_add_left S, ha0, hb0, add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha0⟩
    exact ⟨Subgroup.inv_mem _ ha, by rw [(split_model S).inv_left]; exact ha0⟩

theorem mem_AxQ {c : Ut T M V₁ Mc} :
    c ∈ AxQ S ↔ c ∈ Et2 T M V₁ Mc y t₁ ∧ bet S.cx c (aa S) = 0 := Iff.rfl

theorem AxQ_le : AxQ S ≤ Et2 T M V₁ Mc y t₁ := fun _ h => h.1

theorem card_AxQ : Nat.card (AxQ S) = 2 ^ (s + 1) := by
  have hsplit := split_model S
  let χ : ↥(Et2 T M V₁ Mc y t₁) →* Multiplicative (ZMod 2) :=
    MonoidHom.mk' (fun q => Multiplicative.ofAdd (bet S.cx (q : Ut T M V₁ Mc) (aa S))) (fun a b => by
      show Multiplicative.ofAdd (bet S.cx ((a : Ut T M V₁ Mc) * b) (aa S)) = _
      rw [bet_add_left S]
      rfl)
  have hker : χ.ker = (AxQ S).subgroupOf (Et2 T M V₁ Mc y t₁) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_AxQ]
    constructor
    · intro h
      exact ⟨q.2, ofAdd_eq_one.1 h⟩
    · intro h
      exact ofAdd_eq_one.2 h.2
  have hrange : χ.range = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
    rcases hz z with rfl | rfl
    · exact ⟨1, by simp [χ, hsplit.one_left]⟩
    · exact ⟨⟨w0 S, w0_mem S⟩, by simp [χ, w0_bet S]⟩
  have h1 : χ.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top]
    simp
  have h2 := Subgroup.card_mul_index χ.ker
  rw [h1, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (AxQ_le S)).toEquiv,
    card_Et2 S] at h2
  have h3 : 2 ^ (s + 2) = 2 ^ (s + 1) * 2 := by ring
  rw [h3] at h2
  omega

theorem exists_PX_of_c {c : Ut T M V₁ Mc} (hc : c ∈ AxQ S) :
    ∃ g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y), g (w0 S) * (w0 S)⁻¹ = c := by
  have hsplit := split_model S
  obtain ⟨x, hx, hρ⟩ := exists_rhoX S (fun q => bet S.cx c q)
    (fun e _ e' _ => hsplit.add_right _ e e') hc.2
  refine ⟨rhoX S hx, (mem_XS S).2 ⟨x, hx, rfl⟩, ?_⟩
  have hOO := rhoX_isOO S hx
  have hfix := rhoX_fix_aa S hx
  have htr := rhoX_tr₁ S hx
  refine hsplit.pair_ext ((Et2 T M V₁ Mc y t₁).mul_mem (hOO.map₂ _ (w0_mem S))
    ((Et2 T M V₁ Mc y t₁).inv_mem (w0_mem S))) hc.1 fun e he => ?_
  rw [hsplit.contra_pair hOO hfix htr e he, w0_bet S, mul_one]
  have h := hρ e he
  by_cases h0 : bet S.cx c e = 0
  · rw [h0, sm_zero, mul_one] at h
    rw [h0]
    exact phi_eq_zero_iff.2 h
  · have h1 := zmod_two_eq_one h0
    rw [h1, sm_one] at h
    rw [h1]
    refine phi_eq_one_iff.2 fun hh => ?_
    have h2 : e * aa S = e := h.symm.trans hh
    exact aa_ne_one S (mul_eq_left.1 h2)

theorem card_PX : Nat.card (XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) = 2 ^ (s + 1) := by
  rw [← card_AxQ S]
  have hsplit := split_model S
  let f : ↥(XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) → ↥(AxQ S) := fun g =>
    ⟨(g : MulAut (Ut T M V₁ Mc)) (w0 S) * (w0 S)⁻¹,
      (Et2 T M V₁ Mc y t₁).mul_mem ((PX_isOO S g.2).map₂ _ (w0_mem S))
        ((Et2 T M V₁ Mc y t₁).inv_mem (w0_mem S)),
      hsplit.contra_perp (PX_isOO S g.2) (PX_fix S g.2)⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun g g' hgg => ?_, fun c => ?_⟩)
  · have hc : (g : MulAut (Ut T M V₁ Mc)) (w0 S) * (w0 S)⁻¹ = (g' : MulAut (Ut T M V₁ Mc)) (w0 S) *
        (w0 S)⁻¹ := congrArg Subtype.val hgg
    apply Subtype.ext
    refine hsplit.determ₂ (PX_isOO S g.2).swap (PX_isOO S g'.2).swap fun w hw => ?_
    rw [hsplit.contra (PX_isOO S g.2) (PX_fix S g.2) (PX_tr₁ S g.2) (w0_mem S) (w0_bet S) hw,
      hsplit.contra (PX_isOO S g'.2) (PX_fix S g'.2) (PX_tr₁ S g'.2) (w0_mem S) (w0_bet S) hw, hc]
  · obtain ⟨g, hg, hgc⟩ := exists_PX_of_c S c.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgc⟩

theorem tau_sq : ∃ c' : ↥(NZ T), (c' : G) ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) ∧
    tau S * tau S = rho S.cx c' := by
  obtain ⟨u, huU, c', hc', hsq⟩ := sq_mem_UCT S.cx S.c.h51 S.c.h52 (t₁_mem_T S)
  have hc'N : c' ∈ NZ T := Mc_le_NZ S.cx (T_le_Mc S.cx hc'.1)
  have huN : u ∈ NZ T := Mc_le_NZ S.cx (T_le_Mc S.cx (U_le_T S.cx huU))
  refine ⟨⟨c', hc'N⟩, hc', ?_⟩
  unfold tau
  rw [← map_mul]
  have e : (⟨t₁, t₁_mem_NZ' S⟩ * ⟨t₁, t₁_mem_NZ' S⟩ : NZ T) = ⟨u, huN⟩ * ⟨c', hc'N⟩ :=
    Subtype.ext hsq
  rw [e, map_mul, rho_eq_one_of_mem_U S.cx ⟨u, huN⟩ huU, one_mul]

theorem tau_conj_PX {g : MulAut (Ut T M V₁ Mc)}
    (hg : g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) :
    tau S * g * (tau S)⁻¹ ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) := by
  obtain ⟨c', hc', htt⟩ := tau_sq S
  have hg₁ : (tau S * tau S) * g * (tau S * tau S)⁻¹ ∈
      XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) := by
    rw [htt]
    obtain ⟨x, hx, rfl⟩ := (mem_XS S).1 hg
    have hmem := conj_normalizes_X S.cx S.hy hc' x hx
    have e : rho S.cx c' * rhoX S hx * (rho S.cx c')⁻¹ =
        rho S.cx (c' * ⟨x, X_le_NZ S hx⟩ * c'⁻¹) := by
      simp [rhoX, map_mul, map_inv]
    rw [e]
    exact rho_mem_XStar S.cx _ (by simpa using hmem)
  refine (mem_QX S).2 ⟨_, hg₁, ?_⟩
  group

theorem QX_eq_conj : XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) =
    conjSubgroup (XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) (tau S) := by
  ext h
  rw [mem_QX S, mem_conjSubgroup_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have e : tau S * ((tau S)⁻¹ * g * tau S) * (tau S)⁻¹ = g := by group
    rw [e]
    exact hg
  · intro hh
    refine ⟨tau S * h * (tau S)⁻¹, hh, ?_⟩
    group

theorem card_QX : Nat.card (XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) =
    2 ^ (s + 1) := by
  rw [QX_eq_conj S, card_conjSubgroup', card_PX S]

theorem QX_comm {h h' : MulAut (Ut T M V₁ Mc)}
    (hh : h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁))
    (hh' : h' ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) : h * h' = h' * h := by
  obtain ⟨g, hg, rfl⟩ := (mem_QX S).1 hh
  obtain ⟨g', hg', rfl⟩ := (mem_QX S).1 hh'
  have := PX_comm S hg hg'
  calc (tau S)⁻¹ * g * tau S * ((tau S)⁻¹ * g' * tau S) = (tau S)⁻¹ * (g * g') * tau S := by group
    _ = (tau S)⁻¹ * (g' * g) * tau S := by rw [this]
    _ = (tau S)⁻¹ * g' * tau S * ((tau S)⁻¹ * g * tau S) := by group

theorem comm_QX_PX {g h : MulAut (Ut T M V₁ Mc)}
    (hg : g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y))
    (hh : h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) :
    ⁅h, g⁆ ∈ XStar153 T M V₁ Mc (VZ T M) := by
  obtain ⟨ν, hν, hν1, huniq⟩ := exists_nu S
  have hνP := VS_le_XS S (y := y) (t₁ := t₁) hν
  have hsplit := split_model S
  have key := hsplit.comm_abs (ν := ν) (w₀ := w0 S) (PX_isOO S hg) (PX_fix S hg) (PX_tr₁ S hg)
    (PX_sq S hg) (QX_isOO S hh) (QX_fix S hh) (QX_tr₂ S hh) (QX_sq S hh) (aq_mem_Et2 S)
    (bet_aq_aa S) (w0_mem S) (w0_bet S) (PX_isOO S hνP) (nu_E2 S hν hν1)
  rcases key with h1 | h1
  · rw [commutatorElement_def, h1]
    exact Subgroup.one_mem _
  · rw [commutatorElement_def, h1]
    exact hν

theorem radQ {h : MulAut (Ut T M V₁ Mc)}
    (hh : h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁))
    (hcomm : ∀ g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y), h * g = g * h) :
    h ∈ XStar153 T M V₁ Mc (VZ T M) := by
  obtain ⟨ν, hν, hν1, huniq⟩ := exists_nu S
  have hνP := VS_le_XS S (y := y) (t₁ := t₁) hν
  have hsplit := split_model S
  rcases hsplit.rad_full (ν := ν) (w₀ := w0 S) (QX_isOO S hh) (QX_fix S hh) (QX_tr₂ S hh)
    (QX_sq S hh) (aq_mem_Et2 S) (aq_ne_one S) (bet_aq_aa S) (w0_mem S) (w0_bet S)
    (PX_isOO S hνP) (nu_E2 S hν hν1) (fun c hc hca => by
      obtain ⟨g, hg, hgc⟩ := exists_PX_of_c S (c := c) ⟨hc, hca⟩
      exact ⟨g, PX_isOO S hg, PX_fix S hg, PX_tr₁ S hg, PX_sq S hg, hgc, hcomm g hg⟩) with h1 | h1
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [h1]
    exact hν

theorem radP {g : MulAut (Ut T M V₁ Mc)} (hg : g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y))
    (hcomm : ∀ h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁), h * g = g * h) :
    g ∈ XStar153 T M V₁ Mc (VZ T M) := by
  have h2 : tau S * g * (tau S)⁻¹ ∈ XStar153 T M V₁ Mc (VZ T M) := by
    refine radQ S (tau_conj_PX S hg) fun g' hg' => ?_
    have hh : (tau S)⁻¹ * g' * tau S ∈
        XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) := (mem_QX S).2 ⟨g', hg', rfl⟩
    have h3 := hcomm _ hh
    calc tau S * g * (tau S)⁻¹ * g' = tau S * (g * ((tau S)⁻¹ * g' * tau S)) * (tau S)⁻¹ := by group
      _ = tau S * (((tau S)⁻¹ * g' * tau S) * g) * (tau S)⁻¹ := by rw [← h3]
      _ = g' * (tau S * g * (tau S)⁻¹) := by group
  have h4 := tauInv_conj_VS S h2
  have e : (tau S)⁻¹ * (tau S * g * (tau S)⁻¹) * tau S = g := by group
  rwa [e] at h4

theorem D8s_field : IsD8Power153 s (XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ⊔
    XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) := by
  have hint := inter_field S
  refine isD8Power_of_pair s _ _ (XStar153 T M V₁ Mc (VZ T M)) (card_Vstar_field S)
    (VS_le_XS S) (by rw [← hint]; exact inf_le_right) (by rw [hint])
    (fun a ha b hb => PX_comm S ha hb) (fun a ha => PX_sq S ha)
    (fun a ha b hb => QX_comm S ha hb) (fun a ha => QX_sq S ha)
    (fun g hg h hh => comm_QX_PX S hg hh) (fun h hh hc => radQ S hh hc)
    (fun g hg hc => radP S hg hc) (card_PX S) (card_QX S)

end D8

end S153E56p

end CFSG.Quasithin
