module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec
public import CFSG.Quasithin.Vol2.Asc94.He42BaseFacts
public import CFSG.Quasithin.Vol2.Asc94.He42SE6

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

section Finite

theorem he42p_fin_le4_422 : ∀ P Q : GL2, P ^ 3 = 1 → Q ^ 3 = 1 → (P ≠ 1 ∨ Q ≠ 1) →
    (Finset.univ.filter (fun M : M2 => P.val * M * Q.valᵀ = M)).card *
      (Finset.univ.filter (fun v : V2 => P.val *ᵥ v = v)).card *
      (Finset.univ.filter (fun v : V2 => Q.val *ᵥ v = v)).card ≤ 4 := by
  decide +kernel

theorem he42p_fin_cnt_422 : ∀ P Q : GL2, P ^ 3 = 1 → Q ^ 3 = 1 → (P ≠ 1 ∨ Q ≠ 1) →
    (Finset.univ.filter (fun M : M2 => P.val * M * Q.valᵀ = M)).card ∈ ({1, 4} : Finset ℕ) := by
  decide +kernel

end Finite

namespace HeSetup

variable {G : Type} [Group G] [Finite G] (S : HeSetup G)

theorem exists_decomp_422 {j : G} (hj : j ∈ S.J) :
    ∃ p : G × G, p.1 ∈ S.A ∧ p.2 ∈ S.A' ∧ j = p.1 * p.2 := by
  have hcomm : ∀ x ∈ S.A, ∀ y ∈ S.A', x * y * x⁻¹ * y⁻¹ ∈ S.A ⊓ S.A' :=
    fun x hx y hy => (S.hD.hT.comm x hx y hy).1
  refine HeJ.sup_induction (A := S.A) (A' := S.A')
    (P := fun j => ∃ p : G × G, p.1 ∈ S.A ∧ p.2 ∈ S.A' ∧ j = p.1 * p.2) ?_ ?_ ?_ ?_ ?_ hj
  · intro x hx
    exact ⟨(x, 1), hx, S.A'.one_mem, by simp⟩
  · intro x hx
    exact ⟨(1, x), S.A.one_mem, hx, by simp⟩
  · exact ⟨(1, 1), S.A.one_mem, S.A'.one_mem, by simp⟩
  · rintro x y - - ⟨p, hp, hp', rfl⟩ ⟨q, hq, hq', rfl⟩
    have hc : q.1⁻¹ * p.2 * q.1 * p.2⁻¹ ∈ S.A ⊓ S.A' := by
      have := hcomm q.1⁻¹ (S.A.inv_mem hq) p.2 hp'
      simpa only [inv_inv] using this
    refine ⟨(p.1 * q.1 * (q.1⁻¹ * p.2 * q.1 * p.2⁻¹), p.2 * q.2), ?_, ?_, ?_⟩
    · exact S.A.mul_mem (S.A.mul_mem hp hq) (Subgroup.mem_inf.mp hc).1
    · exact S.A'.mul_mem hp' hq'
    · simp only
      group
  · rintro x - ⟨p, hp, hp', rfl⟩
    have he : p.1 * p.2⁻¹ * p.1⁻¹ * p.2 ∈ S.A ⊓ S.A' := by
      have := hcomm p.1 hp p.2⁻¹ (S.A'.inv_mem hp')
      simpa only [inv_inv] using this
    refine ⟨(p.1⁻¹ * (p.1 * p.2⁻¹ * p.1⁻¹ * p.2), p.2⁻¹), ?_, ?_, ?_⟩
    · exact S.A.mul_mem (S.A.inv_mem hp) (Subgroup.mem_inf.mp he).1
    · exact S.A'.inv_mem hp'
    · simp only
      group

theorem u_eq_of_mul_eq_422 {x x' y y' : G} (hx : x ∈ S.A) (hx' : x' ∈ S.A')
    (hy : y ∈ S.A) (hy' : y' ∈ S.A') (h : x * x' = y * y') : S.u x = S.u y := by
  have e : y⁻¹ * x = y' * x'⁻¹ := by
    calc y⁻¹ * x = y⁻¹ * (x * x') * x'⁻¹ := by group
      _ = y⁻¹ * (y * y') * x'⁻¹ := by rw [h]
      _ = y' * x'⁻¹ := by group
  have hz : y⁻¹ * x ∈ S.A ⊓ S.A' :=
    ⟨S.A.mul_mem (S.A.inv_mem hy) hx, by rw [e]; exact S.A'.mul_mem hy' (S.A'.inv_mem hx')⟩
  have h1 : S.u (y * (y⁻¹ * x)) = S.u y + S.u (y⁻¹ * x) :=
    S.hD.hT.cu.mul y hy _ (Subgroup.mem_inf.mp hz).1
  have h2 : S.u (y⁻¹ * x) = 0 :=
    (S.hD.hT.cu.zero _ (Subgroup.mem_inf.mp hz).1).mpr (Subgroup.mem_inf.mp hz).2
  rw [mul_inv_cancel_left, h2, add_zero] at h1
  exact h1

theorem w_eq_of_mul_eq_422 {x x' y y' : G} (hx : x ∈ S.A) (hx' : x' ∈ S.A')
    (hy : y ∈ S.A) (hy' : y' ∈ S.A') (h : x * x' = y * y') : S.w x' = S.w y' := by
  have e : x' * y'⁻¹ = x⁻¹ * y := by
    calc x' * y'⁻¹ = x⁻¹ * (x * x') * y'⁻¹ := by group
      _ = x⁻¹ * (y * y') * y'⁻¹ := by rw [h]
      _ = x⁻¹ * y := by group
  have hz : x' * y'⁻¹ ∈ S.A ⊓ S.A' :=
    ⟨by rw [e]; exact S.A.mul_mem (S.A.inv_mem hx) hy, S.A'.mul_mem hx' (S.A'.inv_mem hy')⟩
  have h1 : S.w (x' * y'⁻¹ * y') = S.w (x' * y'⁻¹) + S.w y' :=
    S.hD.hT.cw.mul _ (Subgroup.mem_inf.mp hz).2 _ hy'
  have h2 : S.w (x' * y'⁻¹) = 0 :=
    (S.hD.hT.cw.zero _ (Subgroup.mem_inf.mp hz).2).mpr (Subgroup.mem_inf.mp hz).1
  rw [inv_mul_cancel_right, h2, zero_add] at h1
  exact h1

open Classical in
noncomputable def decJ_422 (j : G) : G × G :=
  if h : ∃ p : G × G, p.1 ∈ S.A ∧ p.2 ∈ S.A' ∧ j = p.1 * p.2 then h.choose else (1, 1)

theorem decJ_spec {j : G} (hj : j ∈ S.J) :
    (S.decJ_422 j).1 ∈ S.A ∧ (S.decJ_422 j).2 ∈ S.A' ∧ j = (S.decJ_422 j).1 * (S.decJ_422 j).2 := by
  have h := S.exists_decomp_422 hj
  unfold decJ_422
  rw [dif_pos h]
  exact h.choose_spec

noncomputable def coordJ_422 (j : G) : V2 × V2 := (S.u (S.decJ_422 j).1, S.w (S.decJ_422 j).2)

theorem coordJ_eq_422 {x x' : G} (hx : x ∈ S.A) (hx' : x' ∈ S.A') :
    S.coordJ_422 (x * x') = (S.u x, S.w x') := by
  have hJ : x * x' ∈ S.J := S.J.mul_mem (le_sup_left (a := S.A) (b := S.A') hx)
    (le_sup_right (a := S.A) (b := S.A') hx')
  have hd := S.decJ_spec hJ
  have h : (S.decJ_422 (x * x')).1 * (S.decJ_422 (x * x')).2 = x * x' := hd.2.2.symm
  exact Prod.ext (S.u_eq_of_mul_eq_422 hd.1 hd.2.1 hx hx' h)
    (S.w_eq_of_mul_eq_422 hd.1 hd.2.1 hx hx' h)

theorem coordJ_one_422 : S.coordJ_422 1 = 0 := by
  have h := S.coordJ_eq_422 S.A.one_mem S.A'.one_mem
  rw [mul_one] at h
  rw [h]
  have h1 : S.u 1 = 0 := S.hD.hT.cu.map_one
  have h2 : S.w 1 = 0 := S.hD.hT.cw.map_one
  simp [h1, h2]

theorem coordJ_mul_422 {j₁ j₂ : G} (h₁ : j₁ ∈ S.J) (h₂ : j₂ ∈ S.J) :
    S.coordJ_422 (j₁ * j₂) = S.coordJ_422 j₁ + S.coordJ_422 j₂ := by
  obtain ⟨a₁, a₁', ha₁, ha₁', e₁⟩ : ∃ a b : G, a ∈ S.A ∧ b ∈ S.A' ∧ j₁ = a * b :=
    ⟨_, _, (S.decJ_spec h₁).1, (S.decJ_spec h₁).2.1, (S.decJ_spec h₁).2.2⟩
  obtain ⟨a₂, a₂', ha₂, ha₂', e₂⟩ : ∃ a b : G, a ∈ S.A ∧ b ∈ S.A' ∧ j₂ = a * b :=
    ⟨_, _, (S.decJ_spec h₂).1, (S.decJ_spec h₂).2.1, (S.decJ_spec h₂).2.2⟩
  have he : a₂⁻¹ * a₁' * a₂ * a₁'⁻¹ ∈ S.A ⊓ S.A' := by
    have := (S.hD.hT.comm a₂⁻¹ (S.A.inv_mem ha₂) a₁' ha₁').1
    simpa only [inv_inv] using this
  have hc₁ : S.coordJ_422 j₁ = (S.u a₁, S.w a₁') := by rw [e₁]; exact S.coordJ_eq_422 ha₁ ha₁'
  have hc₂ : S.coordJ_422 j₂ = (S.u a₂, S.w a₂') := by rw [e₂]; exact S.coordJ_eq_422 ha₂ ha₂'
  have key : j₁ * j₂ = (a₁ * a₂ * (a₂⁻¹ * a₁' * a₂ * a₁'⁻¹)) * (a₁' * a₂') := by
    rw [e₁, e₂]; group
  have hA : a₁ * a₂ * (a₂⁻¹ * a₁' * a₂ * a₁'⁻¹) ∈ S.A :=
    S.A.mul_mem (S.A.mul_mem ha₁ ha₂) (Subgroup.mem_inf.mp he).1
  have hu0 : S.u (a₂⁻¹ * a₁' * a₂ * a₁'⁻¹) = 0 :=
    (S.hD.hT.cu.zero _ (Subgroup.mem_inf.mp he).1).mpr (Subgroup.mem_inf.mp he).2
  have hmul : S.u (a₁ * a₂ * (a₂⁻¹ * a₁' * a₂ * a₁'⁻¹)) = S.u a₁ + S.u a₂ := by
    rw [S.hD.hT.cu.mul _ (S.A.mul_mem ha₁ ha₂) _ (Subgroup.mem_inf.mp he).1,
      S.hD.hT.cu.mul a₁ ha₁ a₂ ha₂, hu0, add_zero]
  rw [key, S.coordJ_eq_422 hA (S.A'.mul_mem ha₁' ha₂'), hc₁, hc₂]
  refine Prod.ext ?_ ?_
  · exact hmul
  · exact S.hD.hT.cw.mul a₁' ha₁' a₂' ha₂'

theorem m_conj_422 {n : G} (hn : n ∈ S.N) {z : G} (hz : z ∈ S.Z) :
    S.m (n * z * n⁻¹) = ((S.rhoG n).1 : M2) * S.m z * ((S.rhoG n).2 : M2)ᵀ := by
  rw [S.rhoG_of_mem hn]
  exact S.hD.hT.m_conj S.N S.hD.hK.norm ⟨n, hn⟩ hz

theorem coordJ_conj_422 {n : G} (hn : n ∈ S.N) {j : G} (hj : j ∈ S.J) :
    S.coordJ_422 (n * j * n⁻¹) =
      (((S.rhoG n).1 : M2) *ᵥ (S.coordJ_422 j).1, ((S.rhoG n).2 : M2) *ᵥ (S.coordJ_422 j).2) := by
  obtain ⟨a, a', ha, ha', e⟩ : ∃ a b : G, a ∈ S.A ∧ b ∈ S.A' ∧ j = a * b :=
    ⟨_, _, (S.decJ_spec hj).1, (S.decJ_spec hj).2.1, (S.decJ_spec hj).2.2⟩
  have hnA := S.hD.hK.norm n hn
  have hna : n * a * n⁻¹ ∈ S.A := hnA.1 a ha
  have hna' : n * a' * n⁻¹ ∈ S.A' := hnA.2 a' ha'
  have hcj : S.coordJ_422 j = (S.u a, S.w a') := by rw [e]; exact S.coordJ_eq_422 ha ha'
  have hconj : n * j * n⁻¹ = (n * a * n⁻¹) * (n * a' * n⁻¹) := by rw [e]; group
  have hu : S.u (n * a * n⁻¹) = ((S.rhoG n).1 : M2) *ᵥ S.u a := by
    rw [S.rhoG_of_mem hn]; exact S.hD.hT.u_conj S.N S.hD.hK.norm ⟨n, hn⟩ ha
  have hw : S.w (n * a' * n⁻¹) = ((S.rhoG n).2 : M2) *ᵥ S.w a' := by
    rw [S.rhoG_of_mem hn]; exact S.hD.hT.w_conj S.N S.hD.hK.norm ⟨n, hn⟩ ha'
  rw [hconj, S.coordJ_eq_422 hna hna', hcj, hu, hw]

theorem coordJ_eq_zero_iff_422 {j : G} (hj : j ∈ S.J) : S.coordJ_422 j = 0 ↔ j ∈ S.A ⊓ S.A' := by
  obtain ⟨a, a', ha, ha', e⟩ : ∃ a b : G, a ∈ S.A ∧ b ∈ S.A' ∧ j = a * b :=
    ⟨_, _, (S.decJ_spec hj).1, (S.decJ_spec hj).2.1, (S.decJ_spec hj).2.2⟩
  constructor
  · intro h
    rw [e, S.coordJ_eq_422 ha ha'] at h
    have h1 : S.u a = 0 := congrArg Prod.fst h
    have h2 : S.w a' = 0 := congrArg Prod.snd h
    have hx' : a ∈ S.A' := (S.hD.hT.cu.zero a ha).mp h1
    have hx : a' ∈ S.A := (S.hD.hT.cw.zero a' ha').mp h2
    rw [e]
    exact Subgroup.mem_inf.mpr ⟨S.A.mul_mem ha hx, S.A'.mul_mem hx' ha'⟩
  · intro hj'
    have hj'' := Subgroup.mem_inf.mp hj'
    have h := S.coordJ_eq_422 hj''.1 S.A'.one_mem
    rw [mul_one] at h
    rw [h, (S.hD.hT.cu.zero j hj''.1).mpr hj''.2, S.hD.hT.cw.map_one]
    rfl

theorem rhoG_ne_one_422 {y : G} (hyN : y ∈ S.N) (hy3 : orderOf y = 3) : S.rhoG y ≠ 1 := by
  intro h
  have h' : S.rho ⟨y, hyN⟩ = 1 := by rw [← S.rhoG_of_mem hyN]; exact h
  have hk : (⟨y, hyN⟩ : ↥S.N) ∈ (S.hD.hT.rho S.N S.hD.hK.norm).ker := MonoidHom.mem_ker.mpr h'
  rw [S.hD.hT.ker_rho S.hD.hK, Subgroup.mem_subgroupOf] at hk
  have hd := orderOf_dvd_natCard (⟨y, hk⟩ : ↥(S.A ⊔ S.A'))
  rw [Subgroup.orderOf_mk, hy3, S.hD.cardJ] at hd
  norm_num at hd

theorem card_centralizer_J_le_four_422 {y : G} (hyN : y ∈ S.N) (hy3 : y ^ 3 = 1)
    (hρ : S.rhoG y ≠ 1) : Nat.card ↥(centralizer ({y} : Set G) ⊓ S.J) ≤ 4 := by
  have hpow : S.rhoG y ^ 3 = 1 := by
    rw [S.rhoG_of_mem hyN, ← map_pow]
    have h3 : (⟨y, hyN⟩ : ↥S.N) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [h3, map_one]
  have hP3 : (S.rhoG y).1 ^ 3 = 1 := by simpa using congrArg Prod.fst hpow
  have hQ3 : (S.rhoG y).2 ^ 3 = 1 := by simpa using congrArg Prod.snd hpow
  have hPQ : (S.rhoG y).1 ≠ 1 ∨ (S.rhoG y).2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hρ (Prod.ext hcon.1 hcon.2)
  let C : Subgroup G := centralizer ({y} : Set G) ⊓ S.J
  let f : ↥C →* Multiplicative (V2 × V2) :=
    { toFun := fun c => Multiplicative.ofAdd (S.coordJ_422 c.1)
      map_one' := by
        show Multiplicative.ofAdd (S.coordJ_422 1) = 1
        rw [S.coordJ_one_422]; rfl
      map_mul' := fun c d => by
        show Multiplicative.ofAdd (S.coordJ_422 (c.1 * d.1)) =
          Multiplicative.ofAdd (S.coordJ_422 c.1) * Multiplicative.ofAdd (S.coordJ_422 d.1)
        rw [S.coordJ_mul_422 (Subgroup.mem_inf.mp c.2).2 (Subgroup.mem_inf.mp d.2).2]
        rfl }
  have hkmem : ∀ c : ↥f.ker, c.1.1 ∈ S.A ⊓ S.A' ∧ y * c.1.1 * y⁻¹ = c.1.1 := by
    intro c
    have hc0 : S.coordJ_422 c.1.1 = 0 := ofAdd_eq_one.mp (MonoidHom.mem_ker.mp c.2)
    have hJ : c.1.1 ∈ S.J := (Subgroup.mem_inf.mp c.1.2).2
    have hcy : c.1.1 * y = y * c.1.1 := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.1.2).1
    exact ⟨(S.coordJ_eq_zero_iff_422 hJ).mp hc0, (mul_inv_eq_iff_eq_mul).2 hcy.symm⟩
  have hM : ∀ c : ↥f.ker, ((S.rhoG y).1 : M2) * S.m c.1.1 * ((S.rhoG y).2 : M2)ᵀ = S.m c.1.1 := by
    intro c
    have h := S.m_conj_422 hyN (hkmem c).1
    rw [(hkmem c).2] at h
    exact h.symm
  have hinj : Function.Injective (fun c : ↥f.ker =>
      (⟨S.m c.1.1, hM c⟩ : {M : M2 // ((S.rhoG y).1 : M2) * M * ((S.rhoG y).2 : M2)ᵀ = M})) := by
    intro c d h
    have h1 : S.m c.1.1 = S.m d.1.1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    exact S.hD.hT.minj _ (hkmem c).1 _ (hkmem d).1 h1
  have hkerle : Nat.card ↥f.ker ≤
      (Finset.univ.filter (fun M : M2 => (S.rhoG y).1.val * M * (S.rhoG y).2.valᵀ = M)).card := by
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card {M : M2 // ((S.rhoG y).1 : M2) * M * ((S.rhoG y).2 : M2)ᵀ = M} =
        (Finset.univ.filter (fun M : M2 => (S.rhoG y).1.val * M * (S.rhoG y).2.valᵀ = M)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h1.trans h2.le
  have hfix : ∀ v ∈ f.range, (S.rhoG y).1.val *ᵥ (Multiplicative.toAdd v).1 = (Multiplicative.toAdd v).1 ∧
      (S.rhoG y).2.val *ᵥ (Multiplicative.toAdd v).2 = (Multiplicative.toAdd v).2 := by
    intro v hv
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hv
    have hcy : y * c.1 * y⁻¹ = c.1 :=
      (mul_inv_eq_iff_eq_mul).2 (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).1).symm
    have key := S.coordJ_conj_422 hyN (Subgroup.mem_inf.mp c.2).2
    rw [hcy] at key
    have e : Multiplicative.toAdd (f c) = S.coordJ_422 c.1 := rfl
    rw [e]
    exact ⟨(congrArg Prod.fst key).symm, (congrArg Prod.snd key).symm⟩
  let ψ : ↥f.range → {v : V2 // (S.rhoG y).1.val *ᵥ v = v} × {w : V2 // (S.rhoG y).2.val *ᵥ w = w} :=
    fun v => (⟨(Multiplicative.toAdd v.1).1, (hfix v.1 v.2).1⟩, ⟨(Multiplicative.toAdd v.1).2, (hfix v.1 v.2).2⟩)
  have hψ : Function.Injective ψ := by
    intro v w h
    have h1 : (Multiplicative.toAdd v.1).1 = (Multiplicative.toAdd w.1).1 := congrArg (fun p => p.1.1) h
    have h2 : (Multiplicative.toAdd v.1).2 = (Multiplicative.toAdd w.1).2 := congrArg (fun p => p.2.1) h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact Prod.ext h1 h2
  have hrange : Nat.card ↥f.range ≤
      (Finset.univ.filter (fun v : V2 => (S.rhoG y).1.val *ᵥ v = v)).card *
        (Finset.univ.filter (fun v : V2 => (S.rhoG y).2.val *ᵥ v = v)).card := by
    have h1 := Nat.card_le_card_of_injective ψ hψ
    have e1 : Nat.card {v : V2 // (S.rhoG y).1.val *ᵥ v = v} =
        (Finset.univ.filter (fun v : V2 => (S.rhoG y).1.val *ᵥ v = v)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have e2 : Nat.card {w : V2 // (S.rhoG y).2.val *ᵥ w = w} =
        (Finset.univ.filter (fun w : V2 => (S.rhoG y).2.val *ᵥ w = w)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Nat.card_prod, e1, e2] at h1
    exact h1
  have hcard : Nat.card ↥C = Nat.card ↥f.ker * Nat.card ↥f.range := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥C ⧸ f.ker) = Nat.card ↥f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [h2] at h1
    rw [h1, mul_comm]
  have hfin := he42p_fin_le4_422 (S.rhoG y).1 (S.rhoG y).2 hP3 hQ3 hPQ
  show Nat.card ↥C ≤ 4
  rw [hcard]
  calc Nat.card ↥f.ker * Nat.card ↥f.range
      ≤ (Finset.univ.filter (fun M : M2 => (S.rhoG y).1.val * M * (S.rhoG y).2.valᵀ = M)).card *
        ((Finset.univ.filter (fun v : V2 => (S.rhoG y).1.val *ᵥ v = v)).card *
          (Finset.univ.filter (fun v : V2 => (S.rhoG y).2.val *ᵥ v = v)).card) :=
        Nat.mul_le_mul hkerle (hrange.trans le_rfl)
    _ = _ := by ring
    _ ≤ 4 := hfin

theorem centralizer_J_eq_B_422 {y : G} (hyN : y ∈ S.N) (hy3 : y ^ 3 = 1) (hρ : S.rhoG y ≠ 1)
    (hyB : ∀ b ∈ S.B, b * y = y * b) : centralizer ({y} : Set G) ⊓ S.J = S.B := by
  have hB := S.baseFacts
  have hle : S.B ≤ centralizer ({y} : Set G) ⊓ S.J := by
    intro b hb
    have hbZ : b ∈ S.A ⊓ S.A' := (Subgroup.mem_inf.mp hb).1
    exact Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hyB b hb),
      le_sup_left (a := S.A) (b := S.A') (Subgroup.mem_inf.mp hbZ).1⟩
  have hcard : Nat.card ↥(centralizer ({y} : Set G) ⊓ S.J) ≤ Nat.card ↥S.B := by
    rw [hB.card_B]
    exact S.card_centralizer_J_le_four_422 hyN hy3 hρ
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem conj_J_of_Z_422 {n : G} (hZ : ∀ w ∈ S.Z, n * w * n⁻¹ ∈ S.Z)
    (hZ' : ∀ w ∈ S.Z, n⁻¹ * w * n ∈ S.Z)
    (hJ : ∀ c : G, (∀ w ∈ S.Z, w * c = c * w) → c ∈ S.J) :
    ∀ g ∈ S.J, n * g * n⁻¹ ∈ S.J := by
  intro g hg
  apply hJ
  intro w hw
  have hw' := hZ' w hw
  have hc' : (n⁻¹ * w * n) * g = g * (n⁻¹ * w * n) :=
    (HeJ.TData.Z_central S.hD.hT S.hD.hK.Aab S.hD.hK.A'ab hw' hg).symm
  calc w * (n * g * n⁻¹) = n * ((n⁻¹ * w * n) * g) * n⁻¹ := by group
    _ = n * (g * (n⁻¹ * w * n)) * n⁻¹ := by rw [hc']
    _ = (n * g * n⁻¹) * w := by group

theorem mem_N_of_normalizes_Z_422 {n : G} (hZ : ∀ w ∈ S.Z, n * w * n⁻¹ ∈ S.Z)
    (hZ' : ∀ w ∈ S.Z, n⁻¹ * w * n ∈ S.Z)
    (hJ : ∀ c : G, (∀ w ∈ S.Z, w * c = c * w) → c ∈ S.J) : n ∈ S.N := by
  rw [S.hN, Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact conj_J_of_Z_422 S hZ hZ' hJ g hg
  · intro hg
    have h := conj_J_of_Z_422 S (n := n⁻¹) (by simpa using hZ') (by simpa using hZ) hJ _ hg
    have e : n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g := by group
    rw [e] at h
    exact h

theorem centralizer_Z_le_J_422 {z : G} (hzZ : z ∈ S.Z)
    (hP : IsPGroup 2 ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (S.B : Set G)))
    (c : G) (hc : ∀ w ∈ S.Z, w * c = c * w) : c ∈ S.J := by
  have hB := S.baseFacts
  have hBZ : ∀ b ∈ S.B, b ∈ S.Z := fun b hb => (Subgroup.mem_inf.mp hb).1
  exact S.le_J_of_isPGroup hB hzZ hP (hc z hzZ).symm (fun b hb => (hc b (hBZ b hb)).symm)

end HeSetup

end CFSG.Quasithin.A94.He42
