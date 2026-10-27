module

public import CFSG.Quasithin.EmptyFaithful.S153E56P4

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Model

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}

abbrev Ut (T M V₁ Mc : Subgroup G) : Type :=
  ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))

theorem U_le_NZ_cx (cx : Ctx15350 T Mc M V₁ V₂ t) : UH153 T M V₁ Mc ≤ NZ T :=
  fun _ hu => Mc_le_NZ cx (pCoreOf_le 2 Mc (S153E.U_le_Q cx hu))

@[expose] noncomputable def pi (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ↥(UH153 T M V₁ Mc) →* Ut T M V₁ Mc :=
  MonoidHom.codRestrict ((smk T).comp (Subgroup.inclusion (U_le_NZ_cx cx)))
    (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) (fun u => secMk_mem_secImg u.2)

theorem pi_surj (cx : Ctx15350 T Mc M V₁ V₂ t) : Function.Surjective (pi cx) := by
  intro x
  obtain ⟨u, huU, hux⟩ := mem_secImg.1 x.2
  exact ⟨⟨u, huU⟩, Subtype.ext hux⟩

theorem pi_eq_one_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (u : ↥(UH153 T M V₁ Mc)) :
    pi cx u = 1 ↔ (u : G) ∈ quasithinOmegaOneCenter T := by
  rw [← secMk_eq_one_iff (A := NZ T) (B := quasithinOmegaOneCenter T) (x := ⟨u, U_le_NZ_cx cx u.2⟩)]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem pi_eq_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (u u' : ↥(UH153 T M V₁ Mc)) :
    pi cx u = pi cx u' ↔ (u : G)⁻¹ * u' ∈ quasithinOmegaOneCenter T := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, pi_eq_one_iff]
  rfl

theorem pi_conj (cx : Ctx15350 T Mc M V₁ V₂ t) (n : NZ T) (hn : (n : G) ∈ Mc)
    (u : ↥(UH153 T M V₁ Mc)) :
    pi cx ⟨(n : G) * u * (n : G)⁻¹, U_conj_mem hn u.2⟩ = rho cx n (pi cx u) := by
  apply Subtype.ext
  rw [rho_apply_coe]
  change secMk (NZ T) (quasithinOmegaOneCenter T) ⟨(n : G) * u * (n : G)⁻¹, _⟩ = _
  have : (⟨(n : G) * u * (n : G)⁻¹, U_le_NZ_cx cx (U_conj_mem hn u.2)⟩ : NZ T) =
      n * ⟨u, U_le_NZ_cx cx u.2⟩ * n⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]
  rfl

theorem Ut_comm (cx : Ctx15350 T Mc M V₁ V₂ t) (q q' : Ut T M V₁ Mc) : q * q' = q' * q :=
  Subtype.ext (B2F.isElemAbelian_comm cx.hF.isElemAbelian_tilde q.2 q'.2)

theorem Ut_sq (cx : Ctx15350 T Mc M V₁ V₂ t) (q : Ut T M V₁ Mc) : q * q = 1 := by
  apply Subtype.ext
  have := cx.hF.isElemAbelian_tilde.2 q q.2
  rw [pow_two] at this
  exact this

noncomputable def lift (cx : Ctx15350 T Mc M V₁ V₂ t) (q : Ut T M V₁ Mc) : ↥(UH153 T M V₁ Mc) :=
  Function.surjInv (pi_surj cx) q

theorem pi_lift (cx : Ctx15350 T Mc M V₁ V₂ t) (q : Ut T M V₁ Mc) : pi cx (lift cx q) = q :=
  Function.surjInv_eq (pi_surj cx) q

noncomputable def bet (cx : Ctx15350 T Mc M V₁ V₂ t) (q q' : Ut T M V₁ Mc) : ZMod 2 :=
  comm153 (lift cx q : G) (lift cx q' : G)

variable (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem comm153_congr {u u' v v' : ↥(UH153 T M V₁ Mc)} (h : pi S.cx u = pi S.cx u')
    (h' : pi S.cx v = pi S.cx v') : comm153 (u : G) (v : G) = comm153 (u' : G) (v' : G) := by
  have hU := exPair_U S
  rw [pi_eq_iff] at h h'
  have s1 : comm153 (u' : G) (v' : G) = comm153 (u' : G) (v : G) := by
    have e2 : (v : G) * ((v : G)⁻¹ * v') = v' := by group
    have := hU.comm153_add_right u'.2 v.2 (hU.Z_le h')
    rw [e2, comm153_symm (u' : G) ((v : G)⁻¹ * v'), hU.comm153_Z_left h' u'.2, add_zero] at this
    exact this
  have s2 : comm153 (u' : G) (v : G) = comm153 (u : G) (v : G) := by
    have e1 : (u : G) * ((u : G)⁻¹ * u') = u' := by group
    have := hU.comm153_mul_Z_left u.2 h v.2
    rw [e1] at this
    exact this
  exact s2.symm.trans s1.symm

theorem bet_pi (u v : ↥(UH153 T M V₁ Mc)) :
    bet S.cx (pi S.cx u) (pi S.cx v) = comm153 (u : G) (v : G) :=
  comm153_congr S (pi_lift S.cx _) (pi_lift S.cx _)

theorem bet_add_left (q q' r : Ut T M V₁ Mc) : bet S.cx (q * q') r = bet S.cx q r + bet S.cx q' r := by
  obtain ⟨u, rfl⟩ := pi_surj S.cx q
  obtain ⟨u', rfl⟩ := pi_surj S.cx q'
  obtain ⟨v, rfl⟩ := pi_surj S.cx r
  rw [← map_mul, bet_pi S, bet_pi S, bet_pi S]
  exact (exPair_U S).comm153_add_left u.2 u'.2 v.2

theorem bet_add_right (q r r' : Ut T M V₁ Mc) : bet S.cx q (r * r') = bet S.cx q r + bet S.cx q r' := by
  obtain ⟨u, rfl⟩ := pi_surj S.cx q
  obtain ⟨v, rfl⟩ := pi_surj S.cx r
  obtain ⟨v', rfl⟩ := pi_surj S.cx r'
  rw [← map_mul, bet_pi S, bet_pi S, bet_pi S]
  exact (exPair_U S).comm153_add_right u.2 v.2 v'.2

theorem bet_symm (q r : Ut T M V₁ Mc) : bet S.cx q r = bet S.cx r q := by
  obtain ⟨u, rfl⟩ := pi_surj S.cx q
  obtain ⟨v, rfl⟩ := pi_surj S.cx r
  rw [bet_pi S, bet_pi S, comm153_symm]

theorem bet_nondeg (q : Ut T M V₁ Mc) (h : ∀ r, bet S.cx q r = 0) : q = 1 := by
  obtain ⟨u, rfl⟩ := pi_surj S.cx q
  rw [pi_eq_one_iff]
  refine (exPair_U S).rad u u.2 fun v hv => ?_
  have := h (pi S.cx ⟨v, hv⟩)
  rw [bet_pi S] at this
  exact comm153_eq_zero_iff.1 this

@[expose] def Et1 (T M V₁ Mc : Subgroup G) (y : G) : Subgroup (Ut T M V₁ Mc) :=
  (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)).subgroupOf
    (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))

@[expose] def Et2 (T M V₁ Mc : Subgroup G) (y t₁ : G) : Subgroup (Ut T M V₁ Mc) :=
  (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)).subgroupOf
    (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))

theorem mem_Et1 {q : Ut T M V₁ Mc} :
    q ∈ Et1 T M V₁ Mc y ↔ ∃ u : ↥(UH153 T M V₁ Mc), (u : G) ∈ Egp153 T M V₁ Mc y ∧ pi S.cx u = q := by
  unfold Et1
  rw [Subgroup.mem_subgroupOf, mem_tilde_iff]
  constructor
  · rintro ⟨n, hnE, hn⟩
    exact ⟨⟨n, E_le_U S hnE⟩, hnE, Subtype.ext hn⟩
  · rintro ⟨u, huE, rfl⟩
    exact ⟨⟨u, U_le_NZ_cx S.cx u.2⟩, huE, rfl⟩

theorem mem_Et2 {q : Ut T M V₁ Mc} :
    q ∈ Et2 T M V₁ Mc y t₁ ↔ ∃ u : ↥(UH153 T M V₁ Mc),
      (u : G) ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁ ∧ pi S.cx u = q := by
  unfold Et2
  rw [Subgroup.mem_subgroupOf, mem_tilde_iff]
  constructor
  · rintro ⟨n, hnE, hn⟩
    exact ⟨⟨n, E'_le_U S hnE⟩, hnE, Subtype.ext hn⟩
  · rintro ⟨u, huE, rfl⟩
    exact ⟨⟨u, U_le_NZ_cx S.cx u.2⟩, huE, rfl⟩

theorem Et1_iso {q q' : Ut T M V₁ Mc} (hq : q ∈ Et1 T M V₁ Mc y) (hq' : q' ∈ Et1 T M V₁ Mc y) :
    bet S.cx q q' = 0 := by
  obtain ⟨u, hu, rfl⟩ := (mem_Et1 S).1 hq
  obtain ⟨u', hu', rfl⟩ := (mem_Et1 S).1 hq'
  rw [bet_pi S]
  exact comm153_eq_zero_iff.2 (commutatorElement_eq_one_iff_mul_comm.2 (E_comm S hu hu'))

theorem Et2_iso {q q' : Ut T M V₁ Mc} (hq : q ∈ Et2 T M V₁ Mc y t₁) (hq' : q' ∈ Et2 T M V₁ Mc y t₁) :
    bet S.cx q q' = 0 := by
  obtain ⟨u, hu, rfl⟩ := (mem_Et2 S).1 hq
  obtain ⟨u', hu', rfl⟩ := (mem_Et2 S).1 hq'
  rw [bet_pi S]
  exact comm153_eq_zero_iff.2 (commutatorElement_eq_one_iff_mul_comm.2 (E'_comm S hu hu'))

theorem Et_disj {q : Ut T M V₁ Mc} (h1 : q ∈ Et1 T M V₁ Mc y) (h2 : q ∈ Et2 T M V₁ Mc y t₁) : q = 1 := by
  unfold Et1 at h1
  unfold Et2 at h2
  rw [Subgroup.mem_subgroupOf] at h1 h2
  have h3 : (q : Gz T) ∈ tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊓
      tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) := ⟨h1, h2⟩
  rw [tilde_inf_E S, Subgroup.mem_bot] at h3
  exact Subtype.ext h3

theorem card_Et1 : Nat.card (Et1 T M V₁ Mc y) = 2 ^ (s + 2) := by
  rw [Et1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (tilde_E_le_U S)).toEquiv, card_tilde_E S]

theorem card_Et2 : Nat.card (Et2 T M V₁ Mc y t₁) = 2 ^ (s + 2) := by
  rw [Et2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (tilde_E'_le_U S)).toEquiv, card_tilde_E' S]

theorem Et_sup_top : Et1 T M V₁ Mc y ⊔ Et2 T M V₁ Mc y t₁ = ⊤ := by
  let _ : CommGroup (Ut T M V₁ Mc) :=
    { (inferInstance : Group (Ut T M V₁ Mc)) with mul_comm := Ut_comm S.cx }
  have h1 := card_sup_mul_card_inf (Et1 T M V₁ Mc y) (Et2 T M V₁ Mc y t₁)
  have h2 : Et1 T M V₁ Mc y ⊓ Et2 T M V₁ Mc y t₁ = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun q hq => Et_disj S hq.1 hq.2
  rw [h2, Subgroup.card_bot, mul_one, card_Et1 S, card_Et2 S, ← pow_add] at h1
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [h1]
  have := card_tilde_U S
  change 2 ^ (s + 2 + (s + 2)) = Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))
  rw [this]
  congr 1
  omega

theorem Et_dec (w : Ut T M V₁ Mc) : ∃ e ∈ Et1 T M V₁ Mc y, ∃ e' ∈ Et2 T M V₁ Mc y t₁, w = e * e' := by
  let _ : CommGroup (Ut T M V₁ Mc) :=
    { (inferInstance : Group (Ut T M V₁ Mc)) with mul_comm := Ut_comm S.cx }
  have h : w ∈ Et1 T M V₁ Mc y ⊔ Et2 T M V₁ Mc y t₁ := by rw [Et_sup_top S]; exact Subgroup.mem_top w
  obtain ⟨e, he, e', he', rfl⟩ := Subgroup.mem_sup.1 h
  exact ⟨e, he, e', he', rfl⟩

theorem split_model : Split (bet S.cx) (Et1 T M V₁ Mc y) (Et2 T M V₁ Mc y t₁) where
  comm := Ut_comm S.cx
  sq := Ut_sq S.cx
  add_left := bet_add_left S
  add_right := bet_add_right S
  symm := bet_symm S
  nondeg := bet_nondeg S
  iso₁ := fun _ hx _ hy => Et1_iso S hx hy
  iso₂ := fun _ hx _ hy => Et2_iso S hx hy
  disj := fun _ hx hx' => Et_disj S hx hx'
  dec := Et_dec S

theorem dsum_field : tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc) =
      tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊔
        tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) ∧
    tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊓
        tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) = ⊥ := by
  refine ⟨le_antisymm (fun w hw => ?_) (sup_le (tilde_E_le_U S) (tilde_E'_le_U S)), tilde_inf_E S⟩
  obtain ⟨e, he, e', he', h⟩ := Et_dec S (y := y) (t₁ := t₁) ⟨w, hw⟩
  have h1 : w = (e : Gz T) * (e' : Gz T) := congrArg Subtype.val h
  have he1 : (e : Gz T) ∈ tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) := by
    unfold Et1 at he
    exact Subgroup.mem_subgroupOf.1 he
  have he2 : (e' : Gz T) ∈ tildeOf (quasithinOmegaOneCenter T)
      (conjSubgroup (Egp153 T M V₁ Mc y) t₁) := by
    unfold Et2 at he'
    exact Subgroup.mem_subgroupOf.1 he'
  rw [h1]
  exact Subgroup.mul_mem_sup he1 he2

end Model

end S153E56p

end CFSG.Quasithin
