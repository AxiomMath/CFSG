module

public import CFSG.Quasithin.H13.L32NLem14333g
public import CFSG.Quasithin.H13.L32NLem14333f

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits CFSG.Quasithin.SL3Model
open scoped commutatorElement MatrixGroups

namespace L14333

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_LT {L T : Subgroup G} {l : G} (hl : l ∈ L) (hlO : l ∈ pCoreOf 2 (L ⊔ T)) :
    l ∈ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 (inf_le_left : L ⊓ pCoreOf 2 (L ⊔ T) ≤ L) ?_
    ((pCoreOf_isPGroup 2 _).to_le inf_le_right) ⟨hl, hlO⟩
  exact fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk)⟩

omit [Finite G] in
theorem comm_mul_eq (t l₁ l₂ : G) :
    t * (l₁ * l₂) * t⁻¹ * (l₁ * l₂)⁻¹ =
      (t * l₁ * t⁻¹ * l₁⁻¹) * (l₁ * (t * l₂ * t⁻¹ * l₂⁻¹) * l₁⁻¹) := by
  group

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem cocycle_V (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) (f : G → G)
    (hfV : ∀ l ∈ L, f l ∈ V)
    (hf : ∀ l₁ ∈ L, ∀ l₂ ∈ L, f (l₁ * l₂) = f l₁ * (l₁ * f l₂ * l₁⁻¹))
    (hfP : ∀ p ∈ pCoreOf 2 L, f p = 1) (hfU : ∀ u ∈ fsuU T V, f u = 1) (hfx : f x = 1) :
    ∃ w ∈ fsuV1 T V, ∀ l ∈ L, f l = w * (l * w * l⁻¹) := by
  obtain ⟨D'⟩ := hyp.natural.nonempty_data
  let St : L3Setting 1 V (fsuV1 T V) L T (l32nH T V) := ⟨hyp, D'⟩
  set F := GaloisField 2 1
  have hF : Nat.card F = 2 := by rw [GaloisField.card 2 1 one_ne_zero]; norm_num
  have : CharP F 2 := inferInstance
  have hfL : ∀ l : ↥L, f l ∈ V := fun l => hfV l l.2
  have hconst : ∀ l l' : ↥L, D'.θ l = D'.θ l' → f l = f l' := by
    intro l l' h
    have hk : l⁻¹ * l' ∈ D'.θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [D'.ker_eq, Subgroup.mem_subgroupOf] at hk
    have hP : ((l⁻¹ * l' : ↥L) : G) ∈ pCoreOf 2 L := inf_pCoreOf_LT (l⁻¹ * l').2 hk
    have e : (l' : G) = l * ((l⁻¹ * l' : ↥L) : G) := by simp
    rw [e, hf _ l.2 _ (l⁻¹ * l').2, hfP _ hP]
    group
  choose lift hlift using D'.surj
  let δ : SL(3, F) → (Fin 3 → F) := fun A => Multiplicative.toAdd (D'.ψ ⟨f (lift A), hfL _⟩)
  have hδθ : ∀ l : ↥L, δ (D'.θ l) = Multiplicative.toAdd (D'.ψ ⟨f l, hfL l⟩) := by
    intro l
    show Multiplicative.toAdd (D'.ψ ⟨f (lift (D'.θ l)), hfL _⟩) = _
    congr 3
    exact hconst _ _ (hlift _)
  have hact : ∀ (l : ↥L) (v : G) (hv : v ∈ V), Multiplicative.toAdd (D'.ψ ⟨(l : G) * v * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (D'.hnorm l.2) v).mp hv⟩) =
      D'.θ l • Multiplicative.toAdd (D'.ψ ⟨v, hv⟩) := by
    intro l v hv
    have h1 := D'.equiv l ⟨v, hv⟩
    rw [natAct3_apply] at h1
    have e : conjAct V ⟨l, D'.hnorm l.2⟩ ⟨v, hv⟩ = ⟨(l : G) * v * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (D'.hnorm l.2) v).mp hv⟩ :=
      Subtype.ext (conjAct_coe_apply V _ _)
    rw [e] at h1
    rw [h1]
    rfl
  have hmulV : ∀ (v w : G) (hv : v ∈ V) (hw : w ∈ V),
      Multiplicative.toAdd (D'.ψ ⟨v * w, V.mul_mem hv hw⟩) =
        Multiplicative.toAdd (D'.ψ ⟨v, hv⟩) + Multiplicative.toAdd (D'.ψ ⟨w, hw⟩) := by
    intro v w hv hw
    rw [← toAdd_mul, ← map_mul]
    rfl
  have hδ : ∀ A B, δ (A * B) = δ A + A • δ B := by
    intro A B
    obtain ⟨l₁, rfl⟩ := D'.surj A
    obtain ⟨l₂, rfl⟩ := D'.surj B
    rw [← map_mul, hδθ, hδθ, hδθ]
    have hl₂ : (l₁ : G) * f l₂ * (l₁ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (D'.hnorm l₁.2) _).mp (hfL l₂)
    have e : f ((l₁ * l₂ : ↥L) : G) = f l₁ * ((l₁ : G) * f l₂ * (l₁ : G)⁻¹) := by
      rw [Subgroup.coe_mul]
      exact hf _ l₁.2 _ l₂.2
    have e' : (⟨f ((l₁ * l₂ : ↥L) : G), hfL _⟩ : ↥V) = ⟨f l₁ * ((l₁ : G) * f l₂ * (l₁ : G)⁻¹),
        V.mul_mem (hfL l₁) hl₂⟩ := Subtype.ext e
    rw [e', hmulV _ _ (hfL l₁) hl₂, hact l₁ _ (hfL l₂)]
  have hUL := c.U_le_L hyp
  have hQ : ∀ q ∈ Qv (vE F 0), δ q = 0 := by
    intro q hq
    rw [← St.Ubar_eq_Qv] at hq
    obtain ⟨u, rfl⟩ := hq
    have hθ : St.betaU u = D'.θ ⟨u, hUL u.2⟩ := by
      rw [L3Setting.betaU_apply]
      exact St.Phi_of_L ⟨u, hUL u.2⟩
    rw [hθ, hδθ]
    have e : (⟨f ((⟨u, hUL u.2⟩ : ↥L) : G), hfL _⟩ : ↥V) = 1 := Subtype.ext (hfU u u.2)
    rw [e, map_one]
    rfl
  have hy : orderOf (D'.θ ⟨x, c.x_mem⟩) = 3 := by
    have h3 : (D'.θ ⟨x, c.x_mem⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, c.x_mem⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using c.x_cube)
      rw [this, map_one]
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exfalso
      have h1 : D'.θ ⟨x, c.x_mem⟩ = 1 := orderOf_eq_one_iff.mp h
      have hk : (⟨x, c.x_mem⟩ : ↥L) ∈ D'.θ.ker := h1
      rw [D'.ker_eq, Subgroup.mem_subgroupOf] at hk
      have hxP := inf_pCoreOf_LT c.x_mem hk
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨x, hxP⟩
      have hk' : x ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      apply c.x_ne_one
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one c.x_cube))
    · exact h
  have hyδ : δ (D'.θ ⟨x, c.x_mem⟩) = 0 := by
    rw [hδθ]
    have e : (⟨f ((⟨x, c.x_mem⟩ : ↥L) : G), hfL _⟩ : ↥V) = 1 := Subtype.ext hfx
    rw [e, map_one]
    rfl
  obtain ⟨p, hpfix, hp⟩ := cocycle_eq_coboundary hF δ hδ hQ hy hyδ
  obtain ⟨cp, hcp⟩ := eq_smul_e0_of_fix hpfix
  set w : ↥V := D'.ψ.symm (Multiplicative.ofAdd p) with hw
  have hwp : Multiplicative.toAdd (D'.ψ w) = p := by rw [hw, MulEquiv.apply_symm_apply]; rfl
  have hwV1 : (w : G) ∈ fsuV1 T V := (D'.line w).mpr ⟨cp, by rw [hwp, hcp]⟩
  refine ⟨w, hwV1, fun l hl => ?_⟩
  have hlw : l * (w : G) * l⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (D'.hnorm hl) _).mp w.2
  have h1 := hp (D'.θ ⟨l, hl⟩)
  rw [hδθ] at h1
  have h2 : Multiplicative.toAdd (D'.ψ ⟨(w : G) * (l * w * l⁻¹), V.mul_mem w.2 hlw⟩) =
      Multiplicative.toAdd (D'.ψ ⟨f l, hfV l hl⟩) := by
    rw [hmulV _ _ w.2 hlw, hact ⟨l, hl⟩ _ w.2, show (⟨(w : G), w.2⟩ : ↥V) = w from rfl, hwp, h1,
      CharTwo.sub_eq_add]
  have h3 := D'.ψ.injective (Multiplicative.toAdd.injective h2)
  exact (congrArg Subtype.val h3).symm

theorem comm_mem_P (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {t : G}
    (ht : t ∈ T) (htP : ∀ p ∈ pCoreOf 2 L, t * p = p * t) {l : G} (hl : l ∈ L) :
    t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  obtain ⟨_, S⟩ := c.setting
  set N := (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) with hN
  have htN : t ∈ N := ⟨Subgroup.mem_sup_right ht,
    Subgroup.mem_centralizer_iff.mpr fun p hp => (htP p hp).symm⟩
  have hLN : L ⊔ T ≤ Subgroup.normalizer (N : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy,
      normalizer_le_normalizer_centralizer'' _
        ((sup_le (le_normalizer_pCoreOf 2 L)
          (c.T_le_normL.trans (normalizer_le_normalizer_pCoreOf 2 L))) hy)⟩
  have h1 : l * t⁻¹ * l⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hLN (Subgroup.mem_sup_left hl)) _).mp (N.inv_mem htN)
  have h2 : t * l * t⁻¹ * l⁻¹ ∈ N := by
    rw [show t * l * t⁻¹ * l⁻¹ = t * (l * t⁻¹ * l⁻¹) by group]
    exact N.mul_mem htN h1
  have h3 : t * l * t⁻¹ * l⁻¹ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (c.T_le_normL ht) l).mp hl
    exact L.mul_mem this (L.inv_mem hl)
  rw [← S.cent_eq]
  refine ⟨h3, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hvP : v ∈ pCoreOf 2 L := (le_sup_left.trans (c.sup_zU_le_P hyp)) hv
  exact Subgroup.mem_centralizer_iff.mp h2.2 v hvP

theorem mem_zU_of_comm_K (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {t : G}
    (ht : t ∈ T) (htK : ∀ k ∈ K, t * k = k * t) : t ∈ centerOf (fsuU T V) := by
  obtain ⟨hP, -⟩ := c.pCoreOf_eq hyp
  have hPab : ∀ u ∈ pCoreOf 2 L, ∀ w ∈ pCoreOf 2 L, u * w = w * u := hP ▸ c.X_comm
  have hsqV : ∀ u ∈ pCoreOf 2 L, u * u ∈ V := hP ▸ c.sq_mem_V_of_X
  have hPK := c.P_le_K hyp
  have hUK := c.U_le_K
  have hdP : d ∈ pCoreOf 2 L := (le_sup_right.trans (c.sup_zU_le_P hyp)) c.d_mem
  have hVP : V ≤ pCoreOf 2 L := le_sup_left.trans (c.sup_zU_le_P hyp)
  have hLP : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hconjP : ∀ l ∈ L, ∀ p ∈ pCoreOf 2 L, l * p * l⁻¹ ∈ pCoreOf 2 L := fun l hl p hp =>
    (Subgroup.mem_normalizer_iff.mp (hLP hl) p).mp hp
  have hcoc : ∀ s ∈ T, (∀ k ∈ K, s * k = k * s) ∨ ((∀ p ∈ pCoreOf 2 L, s * p = p * s) ∧
      (∀ u ∈ fsuU T V, s * u = u * s) ∧ s * x = x * s) →
      ∀ l ∈ L, s * l * s⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro s hs hsK l hl
    have hsP : ∀ p ∈ pCoreOf 2 L, s * p = p * s := by
      rcases hsK with h | h
      · exact fun p hp => h p (hPK hp)
      · exact h.1
    exact c.comm_mem_P hyp hs hsP hl
  have htP : ∀ p ∈ pCoreOf 2 L, t * p = p * t := fun p hp => htK p (hPK hp)
  have htU : ∀ u ∈ fsuU T V, t * u = u * t := fun u hu => htK u (hUK hu)
  have htx : t * x = x * t := htK x c.x_mem_K
  have he : ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 L := fun l hl =>
    hcoc t ht (Or.inl htK) l hl
  have hvanish : ∀ s : G, (∀ p ∈ pCoreOf 2 L, s * p = p * s) → ∀ y : G, s * y = y * s →
      s * y * s⁻¹ * y⁻¹ = 1 := fun s _ y hy => by rw [hy]; group
  obtain ⟨w₁, hw₁, hf₁⟩ := c.cocycle_V hyp (fun l => (t * l * t⁻¹ * l⁻¹) * (t * l * t⁻¹ * l⁻¹))
    (fun l hl => hsqV _ (he l hl))
    (fun l₁ hl₁ l₂ hl₂ => by
      rw [comm_mul_eq]
      have ha := he l₁ hl₁
      have hb := hconjP l₁ hl₁ _ (he l₂ hl₂)
      have hc := hPab _ hb _ ha
      calc (t * l₁ * t⁻¹ * l₁⁻¹ * (l₁ * (t * l₂ * t⁻¹ * l₂⁻¹) * l₁⁻¹)) *
            (t * l₁ * t⁻¹ * l₁⁻¹ * (l₁ * (t * l₂ * t⁻¹ * l₂⁻¹) * l₁⁻¹))
          = t * l₁ * t⁻¹ * l₁⁻¹ * ((l₁ * (t * l₂ * t⁻¹ * l₂⁻¹) * l₁⁻¹) *
            (t * l₁ * t⁻¹ * l₁⁻¹)) * (l₁ * (t * l₂ * t⁻¹ * l₂⁻¹) * l₁⁻¹) := by group
        _ = t * l₁ * t⁻¹ * l₁⁻¹ * ((t * l₁ * t⁻¹ * l₁⁻¹) *
            (l₁ * (t * l₂ * t⁻¹ * l₂⁻¹) * l₁⁻¹)) * (l₁ * (t * l₂ * t⁻¹ * l₂⁻¹) * l₁⁻¹) := by
            rw [hc]
        _ = t * l₁ * t⁻¹ * l₁⁻¹ * (t * l₁ * t⁻¹ * l₁⁻¹) *
            (l₁ * ((t * l₂ * t⁻¹ * l₂⁻¹) * (t * l₂ * t⁻¹ * l₂⁻¹)) * l₁⁻¹) := by group)
    (fun p hp => by rw [hvanish t htP p (htP p hp)]; group)
    (fun u hu => by rw [hvanish t htP u (htU u hu)]; group)
    (by rw [hvanish t htP x htx]; group)
  obtain ⟨d₁, hd₁, hd₁w⟩ : ∃ d₁ ∈ centerOf (fsuU T V), d₁ * d₁ = w₁ := by
    rcases c.eq_of_mem_V1 hw₁ with rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, mul_one 1⟩
    · exact ⟨d, c.d_mem, c.d_sq⟩
  have hd₁P : d₁ ∈ pCoreOf 2 L := (le_sup_right.trans (c.sup_zU_le_P hyp)) hd₁
  set t' := t * d₁⁻¹ with ht'
  have hd₁U : d₁ ∈ fsuU T V := (Subgroup.mem_inf.mp hd₁).1
  have ht'T : t' ∈ T := T.mul_mem ht (T.inv_mem (c.U_le_T hd₁U))
  have htd : t * d₁ = d₁ * t := htU d₁ hd₁U
  have ht'P : ∀ p ∈ pCoreOf 2 L, t' * p = p * t' := by
    intro p hp
    have h1 := hPab _ (inv_mem hd₁P) p hp
    calc t' * p = t * (d₁⁻¹ * p) := by rw [ht']; group
      _ = t * (p * d₁⁻¹) := by rw [h1]
      _ = (t * p) * d₁⁻¹ := by group
      _ = (p * t) * d₁⁻¹ := by rw [htP p hp]
      _ = p * t' := by rw [ht']; group
  have hd₁Z : ∀ u ∈ fsuU T V, d₁ * u = u * d₁ := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd₁).2 u hu).symm
  have ht'U : ∀ u ∈ fsuU T V, t' * u = u * t' := by
    intro u hu
    have h1 : d₁⁻¹ * u = u * d₁⁻¹ := by
      have := hd₁Z u hu
      calc d₁⁻¹ * u = d₁⁻¹ * (u * d₁) * d₁⁻¹ := by group
        _ = d₁⁻¹ * (d₁ * u) * d₁⁻¹ := by rw [this]
        _ = u * d₁⁻¹ := by group
    calc t' * u = t * (d₁⁻¹ * u) := by rw [ht']; group
      _ = t * (u * d₁⁻¹) := by rw [h1]
      _ = (t * u) * d₁⁻¹ := by group
      _ = (u * t) * d₁⁻¹ := by rw [htU u hu]
      _ = u * t' := by rw [ht']; group
  have hd₁x : x * d₁ * x⁻¹ = d₁ := c.x_comm_zU hd₁
  have ht'x : t' * x = x * t' := by
    have h1 : d₁⁻¹ * x = x * d₁⁻¹ := by
      calc d₁⁻¹ * x = (x * d₁ * x⁻¹)⁻¹ * x := by rw [hd₁x]
        _ = x * d₁⁻¹ := by group
    calc t' * x = t * (d₁⁻¹ * x) := by rw [ht']; group
      _ = t * (x * d₁⁻¹) := by rw [h1]
      _ = (t * x) * d₁⁻¹ := by group
      _ = (x * t) * d₁⁻¹ := by rw [htx]
      _ = x * t' := by rw [ht']; group
  have he' : ∀ l ∈ L, t' * l * t'⁻¹ * l⁻¹ ∈ pCoreOf 2 L := fun l hl =>
    hcoc t' ht'T (Or.inr ⟨ht'P, ht'U, ht'x⟩) l hl
  have he'V : ∀ l ∈ L, t' * l * t'⁻¹ * l⁻¹ ∈ V := by
    intro l hl
    refine c.mem_V_of_mul_self hyp (he' l hl) ?_
    have hld : l * d₁ * l⁻¹ ∈ pCoreOf 2 L := hconjP l hl d₁ hd₁P
    have hlw : l * w₁ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (c.L_le_normV hl) w₁).mp (Subgroup.mem_inf.mp hw₁).1
    have e1 : t' * l * t'⁻¹ * l⁻¹ = (t * l * t⁻¹ * l⁻¹) * (d₁⁻¹ * (l * d₁ * l⁻¹)) := by
      have h1 : t * d₁ * t⁻¹ = d₁ := by rw [htd]; group
      calc t' * l * t'⁻¹ * l⁻¹ = (t * d₁⁻¹ * t⁻¹) * (t * l * t⁻¹ * l⁻¹) * (l * (t * d₁ * t⁻¹) * l⁻¹)
            := by rw [ht']; group
        _ = d₁⁻¹ * (t * l * t⁻¹ * l⁻¹) * (l * d₁ * l⁻¹) := by
            rw [h1, show t * d₁⁻¹ * t⁻¹ = d₁⁻¹ by rw [← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv,
              inv_inv, ← mul_assoc, h1]]
        _ = (t * l * t⁻¹ * l⁻¹) * (d₁⁻¹ * (l * d₁ * l⁻¹)) := by
            rw [hPab _ (inv_mem hd₁P) _ (he l hl)]; group
    rw [e1]
    set A := t * l * t⁻¹ * l⁻¹
    set B := d₁⁻¹ * (l * d₁ * l⁻¹)
    have hA := he l hl
    have hB : B ∈ pCoreOf 2 L := mul_mem (inv_mem hd₁P) hld
    have hAB := hPab _ hA _ hB
    have hAA : A * A = w₁ * (l * w₁ * l⁻¹) := hf₁ l hl
    have hBB : B * B = w₁⁻¹ * (l * w₁ * l⁻¹) := by
      have hc := hPab _ (inv_mem hd₁P) _ hld
      show (d₁⁻¹ * (l * d₁ * l⁻¹)) * (d₁⁻¹ * (l * d₁ * l⁻¹)) = _
      calc (d₁⁻¹ * (l * d₁ * l⁻¹)) * (d₁⁻¹ * (l * d₁ * l⁻¹))
          = d₁⁻¹ * ((l * d₁ * l⁻¹) * d₁⁻¹) * (l * d₁ * l⁻¹) := by group
        _ = d₁⁻¹ * (d₁⁻¹ * (l * d₁ * l⁻¹)) * (l * d₁ * l⁻¹) := by rw [← hc]
        _ = (d₁ * d₁)⁻¹ * (l * (d₁ * d₁) * l⁻¹) := by group
        _ = w₁⁻¹ * (l * w₁ * l⁻¹) := by rw [hd₁w]
    have hw₁V : w₁ ∈ V := (Subgroup.mem_inf.mp hw₁).1
    have hcw := c.ctx.V_comm _ hw₁V _ hlw
    calc A * B * (A * B) = (A * A) * (B * B) := by
          calc A * B * (A * B) = A * (B * A) * B := by group
            _ = A * (A * B) * B := by rw [← hAB]
            _ = (A * A) * (B * B) := by group
      _ = w₁ * (l * w₁ * l⁻¹) * (w₁⁻¹ * (l * w₁ * l⁻¹)) := by rw [hAA, hBB]
      _ = w₁ * w₁⁻¹ * ((l * w₁ * l⁻¹) * (l * w₁ * l⁻¹)) := by
          calc w₁ * (l * w₁ * l⁻¹) * (w₁⁻¹ * (l * w₁ * l⁻¹))
              = w₁ * ((l * w₁ * l⁻¹) * w₁⁻¹) * (l * w₁ * l⁻¹) := by group
            _ = w₁ * (w₁⁻¹ * (l * w₁ * l⁻¹)) * (l * w₁ * l⁻¹) := by
                rw [show (l * w₁ * l⁻¹) * w₁⁻¹ = w₁⁻¹ * (l * w₁ * l⁻¹) by
                  calc (l * w₁ * l⁻¹) * w₁⁻¹ = w₁⁻¹ * (w₁ * (l * w₁ * l⁻¹)) * w₁⁻¹ := by group
                    _ = w₁⁻¹ * ((l * w₁ * l⁻¹) * w₁) * w₁⁻¹ := by rw [hcw]
                    _ = w₁⁻¹ * (l * w₁ * l⁻¹) := by group]
            _ = w₁ * w₁⁻¹ * ((l * w₁ * l⁻¹) * (l * w₁ * l⁻¹)) := by group
      _ = 1 := by rw [mul_inv_cancel, one_mul, c.mul_self_V hlw]
  obtain ⟨w₂, hw₂, hf₂⟩ := c.cocycle_V hyp (fun l => t' * l * t'⁻¹ * l⁻¹) he'V
    (fun l₁ _ l₂ _ => comm_mul_eq t' l₁ l₂)
    (fun p hp => hvanish t' ht'P p (ht'P p hp))
    (fun u hu => hvanish t' ht'P u (ht'U u hu))
    (hvanish t' ht'P x ht'x)
  have hw₂V : w₂ ∈ V := (Subgroup.mem_inf.mp hw₂).1
  have hw₂2 : w₂ * w₂ = 1 := c.mul_self_V hw₂V
  have hcent : t' * w₂ ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨T.mul_mem ht'T (c.U_le_T (c.ctx.V_U hw₂V)), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro l hl
    have h1 := hf₂ l hl
    have hw₂t' : t' * w₂ = w₂ * t' := ht'P w₂ (hVP hw₂V)
    have h2 : t' * l * t'⁻¹ = w₂ * l * w₂ := by
      calc t' * l * t'⁻¹ = (t' * l * t'⁻¹ * l⁻¹) * l := by group
        _ = w₂ * (l * w₂ * l⁻¹) * l := by rw [h1]
        _ = w₂ * l * w₂ := by group
    have h3 : t' * w₂ * t'⁻¹ = w₂ := by rw [hw₂t']; group
    have key : (t' * w₂) * l * (t' * w₂)⁻¹ = l := by
      calc (t' * w₂) * l * (t' * w₂)⁻¹ =
            (t' * w₂ * t'⁻¹) * (t' * l * t'⁻¹) * (t' * w₂ * t'⁻¹)⁻¹ := by group
        _ = w₂ * (w₂ * l * w₂) * w₂⁻¹ := by rw [h3, h2]
        _ = (w₂ * w₂) * l * (w₂ * w₂⁻¹) := by group
        _ = l := by rw [hw₂2, mul_inv_cancel]; group
    calc l * (t' * w₂) = (t' * w₂) * l * (t' * w₂)⁻¹ * (t' * w₂) := by rw [key]
      _ = (t' * w₂) * l := by group
  rw [c.centralizer_L_eq_bot hyp, Subgroup.mem_bot] at hcent
  have ht : t = w₂⁻¹ * d₁ := by
    calc t = (t * d₁⁻¹ * w₂) * w₂⁻¹ * d₁ := by group
      _ = w₂⁻¹ * d₁ := by rw [← ht', hcent, one_mul]
  have hV1Z : fsuV1 T V ≤ centerOf (fsuU T V) := c.vZ ▸ inf_le_right
  rw [ht]
  exact mul_mem (inv_mem (hV1Z hw₂)) hd₁

end Ctx

end L14333

end CFSG.Quasithin.H13
