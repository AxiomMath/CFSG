module

public import CFSG.RankThree.GF2n.Stroth80.Sec717RepInputs
public import CFSG.RankThree.GF2n.Stroth80.Sec717RepLinAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

namespace Sec717RepInputs

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  {B : LinearMap.BilinForm K E} {Qf : E → K} {φ : X →* (E ≃ₗ[K] E)}
  {V L Nb Rb : Subgroup X} {T : Submodule K E}

theorem commute_of_sq_eq_one (I : Sec717RepInputs B Qf φ V L Nb Rb T) {y : X}
    (hy : y ∈ normalizer (V : Set X)) (hy2 : y * y = 1) : ∀ a ∈ V, a * y = y * a := by
  obtain ⟨a₀, ha₀, ha₀1⟩ := I.layer.V_ne
  have hya₀ : y * a₀ * y⁻¹ ∈ V := (mem_normalizer_iff.mp hy a₀).mp ha₀
  obtain ⟨c, hc⟩ := (I.root a₀ ha₀ ha₀1).1 _ hya₀
  have hconj : ∀ (a : X) (d : K), opm (φ a) = d • opm (φ a₀) →
      opm (φ (y * a * y⁻¹)) = d • opm (φ (y * a₀ * y⁻¹)) := by
    intro a d hd
    rw [opm_conj_eq, opm_conj_eq, hd]
    ext x
    simp
  have hyy : y * (y * a₀ * y⁻¹) * y⁻¹ = a₀ := by
    have e : y * (y * a₀ * y⁻¹) * y⁻¹ = (y * y) * a₀ * (y * y)⁻¹ := by group
    rw [e, hy2, one_mul, inv_one, mul_one]
  have h2 : opm (φ a₀) = (c * c) • opm (φ a₀) := by
    have h := hconj (y * a₀ * y⁻¹) c hc
    rw [hyy, hc, smul_smul] at h
    exact h
  have hc1 : c = 1 := by
    have h3 : (c * c - 1) • opm (φ a₀) = 0 := by
      rw [sub_smul, ← h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · have h5 : (c - 1) ^ 2 = 0 := by
        have : (c - 1) ^ 2 = c * c - 1 - (2 : K) * (c - 1) := by ring
        rw [this, h4, I.char2]
        ring
      have h6 : c - 1 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h5
      exact sub_eq_zero.mp h6
    · exact absurd h4 (I.opm_ne_zero ha₀ ha₀1)
  rw [hc1, one_smul] at hc
  intro a ha
  obtain ⟨d, hd⟩ := (I.root a₀ ha₀ ha₀1).1 a ha
  have h6 : opm (φ (y * a * y⁻¹)) = opm (φ a) := by
    rw [hconj a d hd, hc, hd]
  have h7 : y * a * y⁻¹ = a := I.eq_of_opm_eq h6
  calc a * y = y * a * y⁻¹ * y := by rw [h7]
    _ = y * a := by group

theorem semilinear (I : Sec717RepInputs B Qf φ V L Nb Rb T) :
    ∀ Y : Subgroup X, Y ≤ normalizer (V : Set X) → (∀ y ∈ Y, y * y = 1) →
      (∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) →
        Nat.card Y ≤ 2 * Nat.card ↥(centralizer (V : Set X) ⊓ Y) := by
  intro Y hYN hY2 _
  have hYC : Y ≤ centralizer (V : Set X) := fun y hy =>
    mem_centralizer_iff.mpr fun a ha => I.commute_of_sq_eq_one (hYN hy) (hY2 y hy) a ha
  rw [inf_eq_right.mpr hYC]
  exact Nat.le_mul_of_pos_left _ (by norm_num)

theorem opm_commutator_Nb (I : Sec717RepInputs B Qf φ V L Nb Rb T) {m z : X} (hm : m ∈ Nb)
    (hz : z ∈ Nb) (x : E) :
    opm (φ ⁅m, z⁆) x = opm (φ m) (opm (φ z) x) - opm (φ z) (opm (φ m) x) := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact opm_commutator_of_lowering (I.layer.Nb_low m hm) (I.layer.Nb_low z hz) x

theorem opm_mul_V (I : Sec717RepInputs B Qf φ V L Nb Rb T) {v w : X} (hv : v ∈ V) (hw : w ∈ V) :
    opm (φ (v * w)) = opm (φ v) + opm (φ w) := by
  ext x
  rw [map_mul, opm_mul_apply_layer, LinearMap.add_apply,
    (I.layer.V_corner v hv).apply_lowering ((I.layer.V_corner w hw).isLayerLowering I.layer.T_le),
    add_zero]

theorem opm_inv_V (I : Sec717RepInputs B Qf φ V L Nb Rb T) {v : X} (hv : v ∈ V) :
    opm (φ v⁻¹) = -opm (φ v) := by
  ext x
  rw [map_inv, opm_inv_apply_of_lowering ((I.layer.V_corner v hv).isLayerLowering I.layer.T_le),
    I.opm_V_sq hv, add_zero, LinearMap.neg_apply]

theorem V_comm_Nb (I : Sec717RepInputs B Qf φ V L Nb Rb T) {v n : X} (hv : v ∈ V) (hn : n ∈ Nb) :
    n * v = v * n :=
  I.Rb_cent n (I.NR hn) v hv

theorem coeff_unique (I : Sec717RepInputs B Qf φ V L Nb Rb T) {a₀ : X} (ha₀ : a₀ ∈ V)
    (ha₀1 : a₀ ≠ 1) {c d : K} (h : c • opm (φ a₀) = d • opm (φ a₀)) : c = d := by
  have h1 : (c - d) • opm (φ a₀) = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exact absurd h2 (I.opm_ne_zero ha₀ ha₀1)

theorem cl (I : Sec717RepInputs B Qf φ V L Nb Rb T) :
    ∀ r ∈ Rb, (∀ l ∈ L, r * l = l * r) → r ∈ L := by
  intro c hcR hcL
  refine I.CNL c ?_ hcL
  by_contra hcN
  let S : Subgroup X :=
    { carrier := {z | z ∈ Rb ∧ ∀ l ∈ L, ∀ x, opm (φ (z * l * z⁻¹)) x - opm (φ l) x ∈ T}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Rb.mul_mem ha hb, fun l hl x => ?_⟩
        have hl' : b * l * b⁻¹ ∈ L := I.Rb_normL b hb l hl
        have e : a * b * l * (a * b)⁻¹ = a * (b * l * b⁻¹) * a⁻¹ := by group
        have h1 := ha' _ hl' x
        have h2 := hb' l hl x
        rw [e]
        have := T.add_mem h1 h2
        rwa [sub_add_sub_cancel] at this
      one_mem' := ⟨Rb.one_mem, fun l _ x => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Rb.inv_mem ha, fun l hl x => ?_⟩
        have hl' : a⁻¹ * l * a⁻¹⁻¹ ∈ L := I.Rb_normL a⁻¹ (Rb.inv_mem ha) l hl
        have h1 := ha' _ hl' x
        have e : a * (a⁻¹ * l * a⁻¹⁻¹) * a⁻¹ = l := by group
        rw [e] at h1
        have := T.neg_mem h1
        rwa [neg_sub] at this }
  have hS : ∀ z, z ∈ S ↔ z ∈ Rb ∧ ∀ l ∈ L, ∀ x, opm (φ (z * l * z⁻¹)) x - opm (φ l) x ∈ T :=
    fun z => Iff.rfl
  have hNS : Nb ≤ S := by
    intro n hn
    refine (hS n).mpr ⟨I.NR hn, fun l hl x => ?_⟩
    have hc : ⁅n, l⁆ ∈ V := I.Nb_comm n hn l (I.LN hl)
    have e : n * l * n⁻¹ = ⁅n, l⁆ * l := by
      simp only [commutatorElement_def]
      group
    rw [e, map_mul, opm_mul_apply_layer]
    have h1 := (I.layer.V_corner _ hc).top x
    have h2 := (I.layer.V_corner _ hc).top (opm (φ l) x)
    have e2 : opm (φ ⁅n, l⁆) x + opm (φ l) x + opm (φ ⁅n, l⁆) (opm (φ l) x) - opm (φ l) x =
        opm (φ ⁅n, l⁆) x + opm (φ ⁅n, l⁆) (opm (φ l) x) := by abel
    rw [e2]
    exact T.add_mem h1 h2
  have hcS : c ∈ S := by
    refine (hS c).mpr ⟨hcR, fun l hl x => ?_⟩
    have e : c * l * c⁻¹ = l := by rw [hcL l hl]; group
    rw [e, sub_self]
    exact T.zero_mem
  have hSn : ∀ r ∈ Rb, ∀ s ∈ S, r * s * r⁻¹ ∈ S := by
    intro r hr s hs
    obtain ⟨hsR, hs'⟩ := (hS s).mp hs
    refine (hS _).mpr ⟨Rb.mul_mem (Rb.mul_mem hr hsR) (Rb.inv_mem hr), fun l hl x => ?_⟩
    have hl₁ : r⁻¹ * l * r⁻¹⁻¹ ∈ L := I.Rb_normL r⁻¹ (Rb.inv_mem hr) l hl
    have e : r * s * r⁻¹ * l * (r * s * r⁻¹)⁻¹ =
        r * (s * (r⁻¹ * l * r⁻¹⁻¹) * s⁻¹) * r⁻¹ := by group
    have e2 : l = r * (r⁻¹ * l * r⁻¹⁻¹) * r⁻¹ := by group
    have e3 : opm (φ l) x = φ r (opm (φ (r⁻¹ * l * r⁻¹⁻¹)) (φ r⁻¹ x)) := by
      rw [← opm_conj φ, ← e2]
    rw [e, opm_conj φ, e3, ← map_sub]
    exact I.layer.Rb_T r hr _ (hs' _ hl₁ _)
  have hSR : S ≤ Rb := fun z hz => ((hS z).mp hz).1
  have hSeq : S = Rb := by
    rcases I.simple S hNS hSR hSn with h | h
    · exact absurd (h ▸ hcS) hcN
    · exact h
  have hLV : ∀ l ∈ L, l ∈ V := by
    intro l hl
    have hlN : l ∈ Nb := I.LN hl
    set D := opm (φ l) with hD
    have hKinv : ∀ r ∈ Rb, ∀ x ∈ T.comap D, φ r x ∈ T.comap D := by
      intro r hr x hx
      have hr' : r⁻¹ ∈ S := hSeq ▸ Rb.inv_mem hr
      have h1 := ((hS _).mp hr').2 l hl x
      rw [opm_conj φ, inv_inv] at h1
      have h2 : φ r⁻¹ (D (φ r x)) ∈ T := by
        have := T.add_mem h1 (hx : D x ∈ T)
        rwa [sub_add_cancel] at this
      have h3 := I.layer.Rb_T r hr _ h2
      rw [phi_apply_inv_apply] at h3
      exact h3
    have hPK : B.orthogonal T ≤ T.comap D := fun x hx => (I.layer.Nb_low l hlN).mid x hx
    set U := B.orthogonal (T.comap D) with hU
    have hUT : U ≤ T := by
      have h := LinearMap.BilinForm.orthogonal_le (B := B) hPK
      rwa [LinearMap.BilinForm.orthogonal_orthogonal I.layer.nondeg I.layer.refl] at h
    have hUinv : ∀ r ∈ Rb, ∀ w ∈ U, φ r w ∈ U := by
      intro r hr w hw
      rw [hU, LinearMap.BilinForm.mem_orthogonal_iff] at hw ⊢
      intro k hk
      have hk' : φ r⁻¹ k ∈ T.comap D := hKinv r⁻¹ (Rb.inv_mem hr) k hk
      have e : k = φ r (φ r⁻¹ k) := (phi_apply_inv_apply φ r k).symm
      rw [e, I.layer.isom]
      exact hw _ hk'
    rcases I.irrT U hUT hUinv with h | h
    ·
      have hKtop : T.comap D = ⊤ := by
        have h' := congrArg (B.orthogonal) h
        rw [hU, LinearMap.BilinForm.orthogonal_orthogonal I.layer.nondeg I.layer.refl,
          LinearMap.BilinForm.orthogonal_bot] at h'
        exact h'
      have hrange : LinearMap.range D ≤ T := by
        rintro _ ⟨x, rfl⟩
        have : x ∈ T.comap D := hKtop ▸ Submodule.mem_top
        exact this
      have hker : B.orthogonal T ≤ LinearMap.ker D := by
        rw [hD, ker_opm_eq_orthogonal_range B I.layer.nondeg I.layer.refl (φ l) (I.layer.isom l)]
        exact LinearMap.BilinForm.orthogonal_le hrange
      exact I.layer.corner_mem l hlN ⟨fun x => hrange ⟨x, rfl⟩, fun x hx => hker hx⟩
    ·
      exfalso
      have hKP : T.comap D = B.orthogonal T := by
        have h' := congrArg (B.orthogonal) h
        rwa [hU, LinearMap.BilinForm.orthogonal_orthogonal I.layer.nondeg I.layer.refl] at h'
      have hdim := finrank_range_sup_add_finrank_comap D T
      rw [hKP, I.layer.finrank_P, I.layer.finrank_T, I.layer.finrank_E] at hdim
      have hiso : ∀ x ∈ LinearMap.range D ⊔ T, ∀ y ∈ LinearMap.range D ⊔ T, B x y = 0 := by
        have hDP : ∀ e, D e ∈ B.orthogonal T := (I.layer.Nb_low l hlN).top
        intro x hx y hy
        obtain ⟨d, hd, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
        obtain ⟨d', hd', t', ht', rfl⟩ := Submodule.mem_sup.mp hy
        obtain ⟨e, rfl⟩ := hd
        obtain ⟨e', rfl⟩ := hd'
        have h1 : B (D e) (D e') = 0 := I.quadIso l hl l hl e e'
        have h2 : B (D e) t' = 0 :=
          I.layer.refl _ _ ((LinearMap.BilinForm.mem_orthogonal_iff.mp (hDP e)) t' ht')
        have h3 : B t (D e') = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp (hDP e')) t ht
        have h4 : B t t' = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp (I.layer.T_le ht')) t ht
        simp only [map_add, LinearMap.add_apply, h1, h2, h3, h4, add_zero]
      have hle := two_mul_finrank_le_of_isotropic B I.layer.nondeg I.layer.refl _ hiso
      rw [I.layer.finrank_E] at hle
      omega
  obtain ⟨l, hl, hlV⟩ := I.L_ne_V
  exact hlV (hLV l hl)

theorem exists_comm_eq_of_not_mem_L (I : Sec717RepInputs B Qf φ V L Nb Rb T) {z : X}
    (hz : z ∈ Nb) (hzL : z ∉ L) : ∀ w ∈ V, ∃ l ∈ L, ⁅l, z⁆ = w := by
  obtain ⟨a₀, ha₀, ha₀1⟩ := I.layer.V_ne
  obtain ⟨l₀, hl₀, hne⟩ : ∃ l₀ ∈ L, ⁅l₀, z⁆ ≠ 1 := by
    by_contra h
    push Not at h
    apply hzL
    refine I.CNL z hz fun l hl => ?_
    have h1 := h l hl
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hc₀V : ⁅l₀, z⁆ ∈ V := I.Nb_comm l₀ (I.LN hl₀) z hz
  obtain ⟨c₀, hc₀⟩ := (I.root a₀ ha₀ ha₀1).1 _ hc₀V
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc₀
    exact I.opm_ne_zero hc₀V hne hc₀
  intro w hw
  obtain ⟨cw, hcw⟩ := (I.root a₀ ha₀ ha₀1).1 w hw
  obtain ⟨l', hl', hl'D⟩ := I.kL l₀ hl₀ (cw / c₀)
  refine ⟨l', hl', I.eq_of_opm_eq ?_⟩
  have e : opm (φ ⁅l', z⁆) = (cw / c₀) • opm (φ ⁅l₀, z⁆) := by
    ext x
    rw [LinearMap.smul_apply, I.opm_commutator_Nb (I.LN hl') hz,
      I.opm_commutator_Nb (I.LN hl₀) hz, hl'D]
    simp only [LinearMap.smul_apply, map_smul, smul_sub]
  rw [e, hc₀, smul_smul, div_mul_cancel₀ cw hc₀ne, hcw]

theorem nb_semi (I : Sec717RepInputs B Qf φ V L Nb Rb T) :
    ∀ z ∈ Nb, z ∉ V → ∀ w ∈ V, ∃ m ∈ Nb, m * z * m⁻¹ = w * z := by
  intro z hz hzV
  suffices key : ∀ w ∈ V, ∃ m ∈ Nb, ⁅m, z⁆ = w by
    intro w hw
    obtain ⟨m, hm, hmw⟩ := key w hw
    refine ⟨m, hm, ?_⟩
    rw [← hmw, commutatorElement_def]
    group
  by_cases hzL : z ∈ L
  swap
  · intro w hw
    obtain ⟨l, hl, hlw⟩ := I.exists_comm_eq_of_not_mem_L hz hzL w hw
    exact ⟨l, I.LN hl, hlw⟩
  obtain ⟨a₀, ha₀, ha₀1⟩ := I.layer.V_ne
  have hcoeff := I.root a₀ ha₀ ha₀1
  let P : X → K → Prop := fun z' c => ∃ m ∈ Nb, opm (φ ⁅m, z'⁆) = c • opm (φ a₀)
  let Iz : AddSubgroup K :=
    { carrier := {c | P z c}
      add_mem' := by
        rintro c d ⟨m, hm, hmc⟩ ⟨n, hn, hnd⟩
        refine ⟨m * n, Nb.mul_mem hm hn, ?_⟩
        have hmV : ⁅m, z⁆ ∈ V := I.Nb_comm m hm z hz
        have hnV : ⁅n, z⁆ ∈ V := I.Nb_comm n hn z hz
        have e : ⁅m * n, z⁆ = ⁅n, z⁆ * ⁅m, z⁆ := by
          have e1 : ⁅m * n, z⁆ = m * ⁅n, z⁆ * m⁻¹ * ⁅m, z⁆ := by
            simp only [commutatorElement_def]
            group
          rw [e1, I.V_comm_Nb hnV hm]
          group
        rw [e, I.opm_mul_V hnV hmV, hmc, hnd, add_smul, add_comm]
      zero_mem' := ⟨1, Nb.one_mem, by
        rw [show ⁅(1 : X), z⁆ = 1 by simp [commutatorElement_def], map_one, zero_smul]
        ext x
        simp [opm_apply]⟩
      neg_mem' := by
        rintro c ⟨m, hm, hmc⟩
        refine ⟨m⁻¹, Nb.inv_mem hm, ?_⟩
        have hmV : ⁅m, z⁆ ∈ V := I.Nb_comm m hm z hz
        have e : ⁅m⁻¹, z⁆ = ⁅m, z⁆⁻¹ := by
          have e1 : ⁅m⁻¹, z⁆ = m⁻¹ * ⁅m, z⁆⁻¹ * m := by
            simp only [commutatorElement_def]
            group
          rw [e1, I.V_comm_Nb (V.inv_mem hmV) (Nb.inv_mem hm)]
          group
        rw [e, I.opm_inv_V hmV, hmc, neg_smul] }
  have hIz : ∀ c, c ∈ Iz ↔ P z c := fun c => Iff.rfl
  let S : Subgroup X :=
    { carrier := {z' | z' ∈ L ∧ ∀ m ∈ Nb, ∃ c ∈ Iz, opm (φ ⁅m, z'⁆) = c • opm (φ a₀)}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨L.mul_mem ha hb, fun m hm => ?_⟩
        obtain ⟨c, hc, hca⟩ := ha' m hm
        obtain ⟨d, hd, hdb⟩ := hb' m hm
        refine ⟨c + d, Iz.add_mem hc hd, ?_⟩
        have haV : ⁅m, a⁆ ∈ V := I.Nb_comm m hm a (I.LN ha)
        have hbV : ⁅m, b⁆ ∈ V := I.Nb_comm m hm b (I.LN hb)
        have e : ⁅m, a * b⁆ = ⁅m, a⁆ * ⁅m, b⁆ := by
          have e1 : ⁅m, a * b⁆ = ⁅m, a⁆ * (a * ⁅m, b⁆ * a⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [e1, I.V_comm_Nb hbV (I.LN ha)]
          group
        rw [e, I.opm_mul_V haV hbV, hca, hdb, add_smul]
      one_mem' := ⟨L.one_mem, fun m _ => ⟨0, Iz.zero_mem, by
        rw [show ⁅m, (1 : X)⁆ = 1 by simp [commutatorElement_def], map_one, zero_smul]
        ext x
        simp [opm_apply]⟩⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨L.inv_mem ha, fun m hm => ?_⟩
        obtain ⟨c, hc, hca⟩ := ha' m hm
        refine ⟨-c, Iz.neg_mem hc, ?_⟩
        have haV : ⁅m, a⁆ ∈ V := I.Nb_comm m hm a (I.LN ha)
        have e : ⁅m, a⁻¹⁆ = ⁅m, a⁆⁻¹ := by
          have e1 : ⁅m, a⁻¹⁆ = a⁻¹ * ⁅m, a⁆⁻¹ * a := by
            simp only [commutatorElement_def]
            group
          rw [e1, I.V_comm_Nb (V.inv_mem haV) (I.LN (L.inv_mem ha))]
          group
        rw [e, I.opm_inv_V haV, hca, neg_smul] }
  have hS : ∀ z', z' ∈ S ↔ z' ∈ L ∧ ∀ m ∈ Nb, ∃ c ∈ Iz, opm (φ ⁅m, z'⁆) = c • opm (φ a₀) :=
    fun z' => Iff.rfl
  have hVS : V ≤ S := by
    intro v hv
    refine (hS v).mpr ⟨I.VL hv, fun m hm => ⟨0, Iz.zero_mem, ?_⟩⟩
    have e : ⁅m, v⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact I.V_comm_Nb hv hm
    rw [e, zero_smul, map_one]
    ext x
    simp [opm_apply]
  have hSL : S ≤ L := fun z' hz' => ((hS z').mp hz').1
  have hSinv : ∀ r ∈ Rb, ∀ a ∈ S, r * a * r⁻¹ ∈ S := by
    intro r hr a ha
    obtain ⟨haL, ha'⟩ := (hS a).mp ha
    refine (hS _).mpr ⟨I.Rb_normL r hr a haL, fun m hm => ?_⟩
    have hm' : r⁻¹ * m * r⁻¹⁻¹ ∈ Nb := I.Rb_normN r⁻¹ (Rb.inv_mem hr) m hm
    obtain ⟨c, hc, hca⟩ := ha' _ hm'
    refine ⟨c, hc, ?_⟩
    have hV : ⁅r⁻¹ * m * r⁻¹⁻¹, a⁆ ∈ V := I.Nb_comm _ hm' a (I.LN haL)
    have e : ⁅m, r * a * r⁻¹⁆ = ⁅r⁻¹ * m * r⁻¹⁻¹, a⁆ := by
      have e1 : ⁅m, r * a * r⁻¹⁆ = r * ⁅r⁻¹ * m * r⁻¹⁻¹, a⁆ * r⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1, I.Rb_cent r hr _ hV]
      group
    rw [e, hca]
  have hzS : z ∈ S := by
    refine (hS z).mpr ⟨hzL, fun m hm => ?_⟩
    obtain ⟨c, hc⟩ := hcoeff.1 _ (I.Nb_comm m hm z hz)
    exact ⟨c, ⟨m, hm, hc⟩, hc⟩
  have hSeq : S = L := by
    rcases I.invL S hVS hSL hSinv with h | h
    · exact absurd (h ▸ hzS) hzV
    · exact h
  have hall : ∀ c : K, c ∈ Iz := by
    intro c
    obtain ⟨w, hw, hwc⟩ := hcoeff.2 c
    obtain ⟨z₀, hz₀, hz₀L⟩ := I.Nb_ne_L
    obtain ⟨l, hl, hlw⟩ := I.exists_comm_eq_of_not_mem_L hz₀ hz₀L w hw
    have hlS : l ∈ S := hSeq ▸ hl
    obtain ⟨c', hc', hc'l⟩ := ((hS l).mp hlS).2 z₀ hz₀
    have e : ⁅z₀, l⁆ = w := by
      have e1 : ⁅z₀, l⁆ = ⁅l, z₀⁆⁻¹ := (commutatorElement_inv l z₀).symm
      rw [e1, hlw]
      have hww := I.V_sq w hw
      calc w⁻¹ = w⁻¹ * (w * w) := by rw [hww, mul_one]
        _ = w := by group
    rw [e, hwc] at hc'l
    have := I.coeff_unique ha₀ ha₀1 hc'l
    rw [← this] at hc'
    exact hc'
  intro w hw
  obtain ⟨c, hc⟩ := hcoeff.1 w hw
  obtain ⟨m, hm, hmc⟩ := (hIz c).mp (hall c)
  exact ⟨m, hm, I.eq_of_opm_eq (hmc.trans hc.symm)⟩

end Sec717RepInputs

end CFSG.RankThree.GF2n.Stroth80
