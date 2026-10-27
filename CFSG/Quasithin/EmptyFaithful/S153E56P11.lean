module

public import CFSG.Quasithin.EmptyFaithful.S153E56P10
public import CFSG.Quasithin.EmptyFaithful.S153E56P8

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Groups

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem card_Vstar_field : Nat.card (XStar153 T M V₁ Mc (VZ T M)) = 2 := by
  have h := S.cx.hF.card_autOn_tilde (B := VZ T M) S.cx.hF.V_le_H
  exact h.trans S.c.h53two.card_Vstar

theorem mem_XS {g : MulAut (Ut T M V₁ Mc)} :
    g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ↔ ∃ (x : G) (hx : x ∈ Xgp153 T M V₁ Mc y),
      rhoX S hx = g := by
  rw [mem_XStar_iff S.cx]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, X_le_NZ S hx⟩, hx, rfl⟩

theorem rhoX_mul {x x' : G} (hx : x ∈ Xgp153 T M V₁ Mc y) (hx' : x' ∈ Xgp153 T M V₁ Mc y) :
    rhoX S hx * rhoX S hx' = rhoX S ((Xgp153 T M V₁ Mc y).mul_mem hx hx') := by
  unfold rhoX
  rw [← map_mul]
  rfl

theorem rhoX_comm {x x' : G} (hx : x ∈ Xgp153 T M V₁ Mc y) (hx' : x' ∈ Xgp153 T M V₁ Mc y) :
    rhoX S hx * rhoX S hx' = rhoX S hx' * rhoX S hx := by
  have hc : ⁅x, x'⁆ ∈ conjSubgroup (quasithinOmegaOneCenter T) y :=
    (exPair_U' S).comm_mem x (X_le_U' S hx) x' (X_le_U' S hx')
  have h1 : rho S.cx (⟨⁅x, x'⁆, Mc_le_NZ S.cx (U_le_Mc S (S.hG.Z'_le_U hc))⟩ : ↥(NZ T)) = 1 :=
    rho_eq_one_of_mem_U S.cx _ (S.hG.Z'_le_U hc)
  have e : (⟨x * x', X_le_NZ S ((Xgp153 T M V₁ Mc y).mul_mem hx hx')⟩ : ↥(NZ T)) =
      ⟨⁅x, x'⁆, Mc_le_NZ S.cx (U_le_Mc S (S.hG.Z'_le_U hc))⟩ * ⟨x', X_le_NZ S hx'⟩ *
        ⟨x, X_le_NZ S hx⟩ := by
    apply Subtype.ext
    show x * x' = ⁅x, x'⁆ * x' * x
    simp only [commutatorElement_def]
    group
  rw [rhoX_mul S hx hx', rhoX_mul S hx' hx]
  have e2 : rhoX S ((Xgp153 T M V₁ Mc y).mul_mem hx hx') =
      rho S.cx ⟨⁅x, x'⁆, Mc_le_NZ S.cx (U_le_Mc S (S.hG.Z'_le_U hc))⟩ * rho S.cx ⟨x', X_le_NZ S hx'⟩ *
        rho S.cx ⟨x, X_le_NZ S hx⟩ := by
    unfold rhoX
    rw [e, map_mul, map_mul]
  rw [e2, h1, one_mul]
  exact rhoX_mul S hx' hx

theorem rhoX_sq {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y) : rhoX S hx * rhoX S hx = 1 := by
  have hc : x * x ∈ conjSubgroup (quasithinOmegaOneCenter T) y :=
    (exPair_U' S).sq_mem x (X_le_U' S hx)
  rw [rhoX_mul S hx hx]
  exact rho_eq_one_of_mem_U S.cx _ (S.hG.Z'_le_U hc)

theorem V_le_Mc' : VZ T M ≤ Mc := S.cx.hF.V_le_H

theorem V_le_NZ : VZ T M ≤ NZ T := fun _ hv => Mc_le_NZ S.cx (V_le_Mc' S hv)

@[expose] noncomputable def rhoV {v : G} (hv : v ∈ VZ T M) : MulAut (Ut T M V₁ Mc) :=
  rho S.cx ⟨v, V_le_NZ S hv⟩

theorem rhoV_pi {v : G} (hv : v ∈ VZ T M) (u : ↥(UH153 T M V₁ Mc)) :
    rhoV S hv (pi S.cx u) = pi S.cx ⟨v * u * v⁻¹, U_conj_mem (V_le_Mc' S hv) u.2⟩ :=
  (pi_conj S.cx ⟨v, V_le_NZ S hv⟩ (V_le_Mc' S hv) u).symm

theorem conj_V_E {v e : G} (hv : v ∈ VZ T M) (he : e ∈ Egp153 T M V₁ Mc y) :
    v * e * v⁻¹ ∈ Egp153 T M V₁ Mc y :=
  (Subgroup.mem_normalizer_iff.1 (S.hG.V_norm_E hv) e).1 he

theorem conj_V_E' {v e : G} (hv : v ∈ VZ T M) (he : e ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁) :
    v * e * v⁻¹ ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁ := by
  rw [mem_conjSubgroup_iff] at he ⊢
  have h1 := conj_V_E S (conj_t₁_V S hv) he
  have e1 : t₁ * (v * e * v⁻¹) * t₁⁻¹ = (t₁ * v * t₁⁻¹) * (t₁ * e * t₁⁻¹) * (t₁ * v * t₁⁻¹)⁻¹ := by
    group
  rw [e1]
  exact h1

theorem comm_VE {v e : G} (hv : v ∈ VZ T M) (he : e ∈ Egp153 T M V₁ Mc y) :
    ⁅v, e⁆ ∈ quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y := by
  have h1 : ⁅e, v⁆ ∈ ⁅Egp153 T M V₁ Mc y, VZ T M⁆ := Subgroup.commutator_mem_commutator he hv
  have h2 := S.hG.V_comm_E h1
  have h3 := (quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y).inv_mem h2
  rwa [commutatorElement_inv] at h3

theorem rhoV_tr₁ {v : G} (hv : v ∈ VZ T M) :
    ∀ e ∈ Et1 T M V₁ Mc y, rhoV S hv e = e ∨ rhoV S hv e = e * aa S := by
  intro e he
  obtain ⟨u, hu, rfl⟩ := (mem_Et1 S).1 he
  rw [rhoV_pi]
  obtain ⟨z, hz, z', hz', hzz⟩ := (mem_V0_iff S).1 (comm_VE S hv hu)
  have e1 : v * (u : G) * v⁻¹ = ⁅v, (u : G)⁆ * u := by
    simp only [commutatorElement_def]
    group
  have e2 : (⟨v * (u : G) * v⁻¹, U_conj_mem (V_le_Mc' S hv) u.2⟩ : ↥(UH153 T M V₁ Mc)) =
      ⟨z, Z_le_U S hz⟩ * ⟨z', S.hG.Z'_le_U hz'⟩ * u := by
    apply Subtype.ext
    show v * (u : G) * v⁻¹ = z * z' * u
    rw [e1, hzz]
  rw [e2, map_mul, map_mul, (pi_eq_one_iff S.cx _).2 hz, one_mul]
  rcases (mem_Z'_iff S).1 hz' with rfl | rfl
  · left
    have : (⟨1, S.hG.Z'_le_U hz'⟩ : ↥(UH153 T M V₁ Mc)) = 1 := rfl
    rw [this, map_one, one_mul]
  · right
    rw [Ut_comm S.cx, aa_eq]

theorem rhoV_fix_aa {v : G} (hv : v ∈ VZ T M) : rhoV S hv (aa S) = aa S := by
  rw [aa_eq, rhoV_pi]
  congr 1
  apply Subtype.ext
  show v * zp S * v⁻¹ = zp S
  have h := V_comm S hv (Z'_le_V S (zp_mem S))
  rw [h]
  group

theorem rhoV_isOO {v : G} (hv : v ∈ VZ T M) :
    IsOO (bet S.cx) (Et1 T M V₁ Mc y) (Et2 T M V₁ Mc y t₁) (rhoV S hv) where
  iso := bet_rho S (V_le_Mc' S hv)
  map₁ := fun q hq => by
    obtain ⟨u, hu, rfl⟩ := (mem_Et1 S).1 hq
    rw [rhoV_pi]
    exact (mem_Et1 S).2 ⟨_, conj_V_E S hv hu, rfl⟩
  map₂ := fun q hq => by
    obtain ⟨u, hu, rfl⟩ := (mem_Et2 S).1 hq
    rw [rhoV_pi]
    exact (mem_Et2 S).2 ⟨_, conj_V_E' S hv hu, rfl⟩

theorem mem_XS_of_tr₁ {g : MulAut (Ut T M V₁ Mc)}
    (hg : IsOO (bet S.cx) (Et1 T M V₁ Mc y) (Et2 T M V₁ Mc y t₁) g) (hga : g (aa S) = aa S)
    (htr : ∀ e ∈ Et1 T M V₁ Mc y, g e = e ∨ g e = e * aa S) :
    g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) := by
  have hsplit := split_model S
  obtain ⟨x, hx, hρ⟩ := exists_rhoX S (fun e => phi g e)
    (fun e he e' he' => phi_add_on hsplit.comm hsplit.sq (aa_ne_one S) htr he he')
    (phi_eq_zero_iff.2 hga)
  have : rhoX S hx = g := hsplit.determ₁ (rhoX_isOO S hx) hg fun e he => by
    rw [hρ e he, ← tr_eq_sm htr he]
  exact (mem_XS S).2 ⟨x, hx, this⟩

theorem exists_nu : ∃ ν ∈ XStar153 T M V₁ Mc (VZ T M), ν ≠ 1 ∧
    ∀ w ∈ XStar153 T M V₁ Mc (VZ T M), w = 1 ∨ w = ν := by
  obtain ⟨w₀, hw₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(XStar153 T M V₁ Mc (VZ T M)))).1
    (card_Vstar_field S)
  refine ⟨(w₀ : MulAut _), w₀.2, fun h => hw₀ (Subtype.ext h), fun w hw => ?_⟩
  by_cases h1 : w = 1
  · exact Or.inl h1
  · right
    have := huniq ⟨w, hw⟩ (fun h => h1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem mem_VS {g : MulAut (Ut T M V₁ Mc)} (hg : g ∈ XStar153 T M V₁ Mc (VZ T M)) :
    ∃ (v : G) (hv : v ∈ VZ T M), rhoV S hv = g := by
  obtain ⟨n, hn, rfl⟩ := (mem_XStar_iff S.cx _ _).1 hg
  exact ⟨n, hn, rfl⟩

theorem rhoV_mem_XS {v : G} (hv : v ∈ VZ T M) : rhoV S hv ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) :=
  mem_XS_of_tr₁ S (rhoV_isOO S hv) (rhoV_fix_aa S hv) (rhoV_tr₁ S hv)

theorem VS_le_XS : XStar153 T M V₁ Mc (VZ T M) ≤ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) := by
  intro g hg
  obtain ⟨v, hv, rfl⟩ := mem_VS S hg
  exact rhoV_mem_XS S hv

theorem mem_QX {h : MulAut (Ut T M V₁ Mc)} :
    h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) ↔
      ∃ g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y), h = (tau S)⁻¹ * g * tau S :=
  mem_XStar_conj_iff S.cx _ ⟨t₁, t₁_mem_NZ' S⟩ h

theorem tau_conj_VS {g : MulAut (Ut T M V₁ Mc)} (hg : g ∈ XStar153 T M V₁ Mc (VZ T M)) :
    tau S * g * (tau S)⁻¹ ∈ XStar153 T M V₁ Mc (VZ T M) := by
  obtain ⟨n, hn, rfl⟩ := (mem_XStar_iff S.cx _ _).1 hg
  have hmem : t₁ * (n : G) * t₁⁻¹ ∈ VZ T M := conj_t₁_V S hn
  have e : tau S * rho S.cx n * (tau S)⁻¹ =
      rho S.cx (⟨t₁, t₁_mem_NZ' S⟩ * n * ⟨t₁, t₁_mem_NZ' S⟩⁻¹) := by
    unfold tau
    simp [map_mul, map_inv]
  rw [e]
  exact rho_mem_XStar S.cx _ (by simpa using hmem)

theorem tauInv_conj_VS {g : MulAut (Ut T M V₁ Mc)} (hg : g ∈ XStar153 T M V₁ Mc (VZ T M)) :
    (tau S)⁻¹ * g * tau S ∈ XStar153 T M V₁ Mc (VZ T M) := by
  obtain ⟨n, hn, rfl⟩ := (mem_XStar_iff S.cx _ _).1 hg
  have hmem : t₁⁻¹ * (n : G) * t₁ ∈ VZ T M := conj_t₁_inv_V S hn
  have e : (tau S)⁻¹ * rho S.cx n * tau S =
      rho S.cx ((⟨t₁, t₁_mem_NZ' S⟩ : ↥(NZ T))⁻¹ * n * ⟨t₁, t₁_mem_NZ' S⟩) := by
    unfold tau
    simp [map_mul, map_inv]
  rw [e]
  exact rho_mem_XStar S.cx _ (by simpa using hmem)

@[expose] noncomputable def aq : Ut T M V₁ Mc := (tau S)⁻¹ (aa S)

theorem aq_mem_Et2 : aq S ∈ Et2 T M V₁ Mc y t₁ := tauInv_map₁ S _ (aa_mem_Et1 S)

theorem aq_ne_one : aq S ≠ 1 := by
  intro h
  apply aa_ne_one S
  have := congrArg (tau S) h
  rwa [aq, MulAut.apply_inv_self, map_one] at this

theorem tau_aq : tau S (aq S) = aa S := by
  rw [aq, MulAut.apply_inv_self]

theorem tauInv_iso (q q' : Ut T M V₁ Mc) :
    bet S.cx ((tau S)⁻¹ q) ((tau S)⁻¹ q') = bet S.cx q q' := by
  have := tau_iso S ((tau S)⁻¹ q) ((tau S)⁻¹ q')
  rw [MulAut.apply_inv_self, MulAut.apply_inv_self] at this
  exact this.symm

theorem aq_eq : aq S = pi S.cx ⟨t₁⁻¹ * zp S * t₁, conj_t₁_inv_U S (zp_mem_U S)⟩ := by
  rw [aq, aa_eq, tau_inv_pi]

theorem bet_aq_aa : bet S.cx (aq S) (aa S) = 0 := by
  rw [aq_eq, aa_eq, bet_pi S]
  refine comm153_eq_zero_iff.2 (commutatorElement_eq_one_iff_mul_comm.2 ?_)
  exact V_comm S (conj_t₁_inv_V S (Z'_le_V S (zp_mem S))) (Z'_le_V S (zp_mem S))

noncomputable def w0 : Ut T M V₁ Mc := Classical.choose (exists_w₀ S)

theorem w0_mem : w0 S ∈ Et2 T M V₁ Mc y t₁ := (Classical.choose_spec (exists_w₀ S)).1

theorem w0_bet : bet S.cx (w0 S) (aa S) = 1 := (Classical.choose_spec (exists_w₀ S)).2

theorem PX_isOO {g : MulAut (Ut T M V₁ Mc)} (hg : g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) :
    IsOO (bet S.cx) (Et1 T M V₁ Mc y) (Et2 T M V₁ Mc y t₁) g := by
  obtain ⟨x, hx, rfl⟩ := (mem_XS S).1 hg
  exact rhoX_isOO S hx

theorem PX_fix {g : MulAut (Ut T M V₁ Mc)} (hg : g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) :
    g (aa S) = aa S := by
  obtain ⟨x, hx, rfl⟩ := (mem_XS S).1 hg
  exact rhoX_fix_aa S hx

theorem PX_tr₁ {g : MulAut (Ut T M V₁ Mc)} (hg : g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) :
    ∀ e ∈ Et1 T M V₁ Mc y, g e = e ∨ g e = e * aa S := by
  obtain ⟨x, hx, rfl⟩ := (mem_XS S).1 hg
  exact rhoX_tr₁ S hx

theorem PX_sq {g : MulAut (Ut T M V₁ Mc)} (hg : g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) :
    g * g = 1 := by
  obtain ⟨x, hx, rfl⟩ := (mem_XS S).1 hg
  exact rhoX_sq S hx

theorem PX_comm {g g' : MulAut (Ut T M V₁ Mc)}
    (hg : g ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y))
    (hg' : g' ∈ XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) : g * g' = g' * g := by
  obtain ⟨x, hx, rfl⟩ := (mem_XS S).1 hg
  obtain ⟨x', hx', rfl⟩ := (mem_XS S).1 hg'
  exact rhoX_comm S hx hx'

theorem QX_isOO {h : MulAut (Ut T M V₁ Mc)}
    (hh : h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) :
    IsOO (bet S.cx) (Et1 T M V₁ Mc y) (Et2 T M V₁ Mc y t₁) h := by
  obtain ⟨g, hg, rfl⟩ := (mem_QX S).1 hh
  have hOO := PX_isOO S hg
  refine ⟨fun q q' => ?_, fun e he => ?_, fun e he => ?_⟩
  · simp only [MulAut.mul_apply]
    rw [tauInv_iso, hOO.iso, tau_iso]
  · simp only [MulAut.mul_apply]
    exact tauInv_map₂ S _ (hOO.map₂ _ (tau_map₁ S _ he))
  · simp only [MulAut.mul_apply]
    exact tauInv_map₁ S _ (hOO.map₁ _ (tau_map₂ S _ he))

theorem QX_fix {h : MulAut (Ut T M V₁ Mc)}
    (hh : h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) : h (aq S) = aq S := by
  obtain ⟨g, hg, rfl⟩ := (mem_QX S).1 hh
  simp only [MulAut.mul_apply]
  rw [tau_aq, PX_fix S hg]
  rfl

theorem QX_tr₂ {h : MulAut (Ut T M V₁ Mc)}
    (hh : h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) :
    ∀ e ∈ Et2 T M V₁ Mc y t₁, h e = e ∨ h e = e * aq S := by
  obtain ⟨g, hg, rfl⟩ := (mem_QX S).1 hh
  intro e he
  simp only [MulAut.mul_apply]
  rcases PX_tr₁ S hg _ (tau_map₂ S e he) with h1 | h1
  · left
    rw [h1, MulAut.inv_apply_self]
  · right
    rw [h1, map_mul, MulAut.inv_apply_self]
    rfl

theorem QX_sq {h : MulAut (Ut T M V₁ Mc)}
    (hh : h ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) : h * h = 1 := by
  obtain ⟨g, hg, rfl⟩ := (mem_QX S).1 hh
  have := PX_sq S hg
  calc (tau S)⁻¹ * g * tau S * ((tau S)⁻¹ * g * tau S) = (tau S)⁻¹ * (g * g) * tau S := by group
    _ = 1 := by rw [this]; group

theorem nu_mem_QX {ν : MulAut (Ut T M V₁ Mc)} (hν : ν ∈ XStar153 T M V₁ Mc (VZ T M)) :
    ν ∈ XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) := by
  refine (mem_QX S).2 ⟨tau S * ν * (tau S)⁻¹, VS_le_XS S (tau_conj_VS S hν), ?_⟩
  group

theorem nu_E2 {ν : MulAut (Ut T M V₁ Mc)} (hν : ν ∈ XStar153 T M V₁ Mc (VZ T M)) (hν1 : ν ≠ 1) :
    ∀ w ∈ Et2 T M V₁ Mc y t₁, ν w = w * sm (bet S.cx w (aa S)) (aq S) := by
  intro w hw
  have hP := VS_le_XS S hν
  have hQ := nu_mem_QX S hν
  exact (split_model S).nu_formula (PX_isOO S hP) (PX_fix S hP) (PX_tr₁ S hP) (QX_tr₂ S hQ)
    (w0_mem S) (w0_bet S) hν1 hw

theorem inter_field : XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ⊓
    XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) = XStar153 T M V₁ Mc (VZ T M) := by
  obtain ⟨ν, hν, hν1, huniq⟩ := exists_nu S
  have hνQ := nu_mem_QX S hν
  have hVP := VS_le_XS S (y := y) (t₁ := t₁)
  have hVQ : XStar153 T M V₁ Mc (VZ T M) ≤
      XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) := fun w hw => by
    rcases huniq w hw with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hνQ
  refine le_antisymm (fun g hg => ?_) (le_inf hVP hVQ)
  obtain ⟨hgP, hgQ⟩ := hg
  have hνP := hVP hν
  rcases (split_model S).inter_abs (PX_isOO S hgP) (PX_fix S hgP) (PX_tr₁ S hgP) (QX_tr₂ S hgQ)
    (w0_mem S) (w0_bet S) (PX_isOO S hνP) (nu_E2 S hν hν1) with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact hν

end Groups

end S153E56p

end CFSG.Quasithin
