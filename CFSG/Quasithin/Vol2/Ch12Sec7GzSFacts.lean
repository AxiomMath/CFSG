module

public import Certificates.Data.S1277Facts
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSBrV
public import CFSG.Certificates.Kernel.S1277KVlHom
public import CFSG.Certificates.Kernel.S1277KVlSound
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSKap3

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct Certificates.Data.S1277Cand
  Certificates.Data.S1277MLine Certificates.Data.S1277Facts
open CFSG.KS.S1277Vl (det_one_of_mul mul_val_add)
open scoped IsMulCommutative

namespace Fct

theorem comb_add (u : Fin 3 → ℕ) (c c' : Fin 3 → ZMod 2) :
    comb u (c + c') = comb u c ^^^ comb u c' := by
  simp only [comb, Pi.add_apply, mul_val_add]
  simp only [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem comb_zero (u : Fin 3 → ℕ) : comb u 0 = 0 := by simp [comb]

theorem comb_lt {u : Fin 3 → ℕ} (hu : ∀ i, u i < 2 ^ 6) (c : Fin 3 → ZMod 2) :
    comb u c < 2 ^ 6 := by
  have hb : ∀ i, u i * (c i).val < 2 ^ 6 := fun i => by
    have h2 : (c i).val = 0 ∨ (c i).val = 1 := by
      have := ZMod.val_lt (c i)
      omega
    rcases h2 with h | h <;> rw [h]
    · simp
    · simpa using hu i
  unfold comb
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hb 0) (hb 1)) (hb 2)

theorem comb_single (u : Fin 3 → ℕ) (i : Fin 3) : comb u (Pi.single i 1) = u i := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  fin_cases i <;> simp [comb, Pi.single_apply, h1]

theorem inSpan_zero (u : Fin 3 → ℕ) : InSpan u 0 := ⟨0, comb_zero u⟩

theorem inSpan_xor {u : Fin 3 → ℕ} {x y : ℕ} (hx : InSpan u x) (hy : InSpan u y) :
    InSpan u (x ^^^ y) := by
  obtain ⟨e, rfl⟩ := hx
  obtain ⟨e', rfl⟩ := hy
  exact ⟨e + e', comb_add u e e'⟩

def gP (σ : Equiv.Perm (Fin (2 ^ 6))) (x : ℕ) : ℕ :=
  (σ ⟨x % 2 ^ 6, Nat.mod_lt _ (by norm_num)⟩).1

theorem gP_of_lt (σ : Equiv.Perm (Fin (2 ^ 6))) {x : ℕ} (hx : x < 2 ^ 6) :
    gP σ x = (σ ⟨x, hx⟩).1 := by
  simp only [gP, Nat.mod_eq_of_lt hx]

theorem gP_mul (σ τ : Equiv.Perm (Fin (2 ^ 6))) {x : ℕ} (hx : x < 2 ^ 6) :
    gP (σ * τ) x = gP σ (gP τ x) := by
  rw [gP_of_lt _ hx, gP_of_lt _ hx, gP_of_lt _ (τ ⟨x, hx⟩).2, Equiv.Perm.mul_apply]

theorem gP_one {x : ℕ} (hx : x < 2 ^ 6) : gP 1 x = x := by
  rw [gP_of_lt _ hx]
  rfl

theorem gP_xor {φ : ℕ → ℕ} {σ : Equiv.Perm (Fin (2 ^ 6))} (hσ : σ ∈ Sig 6 φ) {x y : ℕ}
    (hx : x < 2 ^ 6) (hy : y < 2 ^ 6) : gP σ (x ^^^ y) = gP σ x ^^^ gP σ y := by
  have hxy : x ^^^ y < 2 ^ 6 := Nat.xor_lt_two_pow hx hy
  rw [gP_of_lt _ hx, gP_of_lt _ hy, gP_of_lt _ hxy]
  exact (hσ.1 ⟨x, hx⟩ ⟨y, hy⟩ ⟨x ^^^ y, hxy⟩ rfl).symm

def PresC (u : Fin 3 → ℕ) (σ : Equiv.Perm (Fin (2 ^ 6))) : Prop :=
  ∀ c, ∃ c', comb u c' = gP σ (comb u c)

noncomputable def linC (u : Fin 3 → ℕ) (σ : Equiv.Perm (Fin (2 ^ 6))) (c : Fin 3 → ZMod 2) :
    Fin 3 → ZMod 2 :=
  if h : ∃ c', comb u c' = gP σ (comb u c) then h.choose else 0

theorem comb_linC {u : Fin 3 → ℕ} {σ : Equiv.Perm (Fin (2 ^ 6))} (hp : PresC u σ)
    (c : Fin 3 → ZMod 2) : comb u (linC u σ c) = gP σ (comb u c) := by
  rw [linC, dif_pos (hp c)]
  exact (hp c).choose_spec

variable {φ : ℕ → ℕ} {u : Fin 3 → ℕ}

noncomputable def linCσ (hu : Basis3 u) {σ : Equiv.Perm (Fin (2 ^ 6))} (hσ : σ ∈ Sig 6 φ)
    (hp : PresC u σ) : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun := linC u σ
  map_add' c c' := by
    apply hu.2
    rw [comb_add, comb_linC hp, comb_linC hp, comb_linC hp, comb_add,
      gP_xor hσ (comb_lt hu.1 c) (comb_lt hu.1 c')]
  map_smul' r c := by
    obtain rfl | rfl : r = 0 ∨ r = 1 := by
      fin_cases r
      exacts [Or.inl rfl, Or.inr rfl]
    · apply hu.2
      rw [zero_smul, RingHom.id_apply, zero_smul, comb_linC hp, comb_zero]
      have hg := gP_xor hσ (x := 0) (y := 0) (by norm_num) (by norm_num)
      rw [Nat.xor_self, Nat.xor_self] at hg
      exact hg
    · rw [one_smul, RingHom.id_apply, one_smul]

theorem linCσ_apply (hu : Basis3 u) {σ : Equiv.Perm (Fin (2 ^ 6))} (hσ : σ ∈ Sig 6 φ)
    (hp : PresC u σ) (c : Fin 3 → ZMod 2) : comb u (linCσ hu hσ hp c) = gP σ (comb u c) :=
  comb_linC hp c

theorem linCσ_congr (hu : Basis3 u) {σ τ : Equiv.Perm (Fin (2 ^ 6))} (e : σ = τ)
    (hσ : σ ∈ Sig 6 φ) (hp : PresC u σ) (hτ : τ ∈ Sig 6 φ) (hq : PresC u τ) :
    linCσ hu hσ hp = linCσ hu hτ hq := by
  subst e
  rfl

theorem linCσ_mul (hu : Basis3 u) {σ τ : Equiv.Perm (Fin (2 ^ 6))} (hσ : σ ∈ Sig 6 φ)
    (hτ : τ ∈ Sig 6 φ) (hστ : σ * τ ∈ Sig 6 φ) (hpσ : PresC u σ) (hpτ : PresC u τ)
    (hpστ : PresC u (σ * τ)) :
    linCσ hu hστ hpστ = (linCσ hu hσ hpσ).comp (linCσ hu hτ hpτ) := by
  refine LinearMap.ext fun c => ?_
  apply hu.2
  rw [LinearMap.comp_apply, linCσ_apply, linCσ_apply, linCσ_apply, gP_mul _ _ (comb_lt hu.1 c)]

theorem linCσ_one (hu : Basis3 u) (h1 : (1 : Equiv.Perm (Fin (2 ^ 6))) ∈ Sig 6 φ)
    (hp : PresC u 1) : linCσ hu h1 hp = LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  apply hu.2
  rw [linCσ_apply, gP_one (comb_lt hu.1 c), LinearMap.id_apply]

section Hom

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G}

theorem sl_hom_span (D : FrData H Q (Phi' Q) 6) (hR : D.rho.range ≤ Sig 6 φ)
    (hQmax : ∀ X : Subgroup G, X ≤ H → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → IsPGroup 2 ↥X →
      X ≤ Q)
    (hQ2 : IsPGroup 2 ↥Q) (hC : ∀ h ∈ H, (∀ x ∈ Q, h * x = x * h) → h ∈ Q)
    (hu : Basis3 u) (hinv : SpanInv D.rho.range u)
    (hker : ∀ σ ∈ D.rho.range, (∀ i (hi : u i < 2 ^ 6), (σ ⟨u i, hi⟩).1 = u i) → σ = 1)
    (h168 : Nat.card D.rho.range = 168) :
    ∃ f : ↥H →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧ f.ker = Q.subgroupOf H := by
  classical
  have hNfr := Phi'_frattini hQ2
  have hsig : ∀ h : ↥H, D.rho h ∈ Sig 6 φ := fun h => hR ⟨h, rfl⟩
  have hpres : ∀ h : ↥H, PresC u (D.rho h) := by
    intro h c
    have hlt := comb_lt hu.1 c
    obtain ⟨c', hc'⟩ := hinv _ ⟨h, rfl⟩ _ hlt ⟨c, rfl⟩
    refine ⟨c', ?_⟩
    rw [gP_of_lt _ hlt]
    exact hc'
  let mat : ↥H → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun h =>
    LinearMap.toMatrix' (linCσ hu (hsig h) (hpres h))
  have hmat_mul : ∀ h h' : ↥H, mat (h * h') = mat h * mat h' := by
    intro h h'
    have hl : linCσ hu (hsig (h * h')) (hpres (h * h')) =
        (linCσ hu (hsig h) (hpres h)).comp (linCσ hu (hsig h') (hpres h')) := by
      have e := linCσ_mul hu (hsig h) (hsig h') (by rw [← map_mul]; exact hsig (h * h'))
        (hpres h) (hpres h') (by rw [← map_mul]; exact hpres (h * h'))
      rw [← e]
      congr 1 <;> rw [map_mul]
    simp only [mat]
    rw [hl, LinearMap.toMatrix'_comp]
  have hmat_one : mat 1 = 1 := by
    have hl : linCσ hu (hsig 1) (hpres 1) = LinearMap.id := by
      have e := linCσ_one hu (φ := φ) (Sig 6 φ).one_mem (by rw [← map_one D.rho]; exact hpres 1)
      rw [← e]
      congr 1 <;> rw [map_one]
    simp only [mat]
    rw [hl, LinearMap.toMatrix'_id]
  have hdet : ∀ h : ↥H, (mat h).det = 1 := fun h =>
    det_one_of_mul (B := mat h⁻¹) (by rw [← hmat_mul, mul_inv_cancel, hmat_one])
  let F : ↥H → Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := fun h => ⟨mat h, hdet h⟩
  have hF : ∀ h h', F (h * h') = F h * F h' := fun h h' => Subtype.ext (hmat_mul h h')
  let f : ↥H →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := MonoidHom.mk' F hF
  have hfval : ∀ h, f h = F h := fun h => rfl
  have hid : ∀ h : ↥H, mat h = 1 → D.rho h = 1 := by
    intro h h1
    have hl : linCσ hu (hsig h) (hpres h) = LinearMap.id := by
      apply LinearMap.toMatrix'.injective
      rw [LinearMap.toMatrix'_id]
      exact h1
    refine hker _ ⟨h, rfl⟩ fun i hi => ?_
    have hc := linCσ_apply hu (hsig h) (hpres h) (Pi.single i 1)
    rw [hl, LinearMap.id_apply, comb_single, gP_of_lt _ hi] at hc
    exact hc.symm
  have hfker : f.ker = Q.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : mat h = 1 := by
        have := congrArg Subtype.val h1
        rw [hfval] at this
        exact this
      exact D.mem_of_rho_eq_one hQmax hQ2 hC hNfr (hid h h2)
    · intro h1
      have h2 : D.rho h = 1 := D.rho_eq_one_of_mem h1
      have h3 : mat h = mat 1 :=
        congrArg LinearMap.toMatrix' (linCσ_congr hu (h2.trans (map_one D.rho).symm) _ _ _ _)
      rw [hfval]
      exact Subtype.ext (h3.trans hmat_one)
  refine ⟨f, ?_, hfker⟩
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card H := Subgroup.card_ker_mul_card_range f
  rw [hfker] at h1
  have h2 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.hQH).toEquiv
  rw [h2] at h1
  have h3 : Nat.card H = Nat.card Q * Nat.card D.rho.range := D.card_H hQmax hQ2 hC hNfr
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h4 : Nat.card f.range = Nat.card D.rho.range := by
    have : Nat.card Q * Nat.card f.range = Nat.card Q * Nat.card D.rho.range := by
      rw [h1, h3]
    exact Nat.eq_of_mul_eq_mul_left hQpos this
  have h6 : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h4, h168, card_sl32]
  exact MonoidHom.range_eq_top.1 h6

theorem sub_span (D : FrData H Q (Phi' Q) 6) (hpre : PreFacts Q D.wc u)
    (hH : ∀ h ∈ H, ∀ x ∈ Q, InSpan u (D.wc x) → InSpan u (D.wc (h * x * h⁻¹))) :
    ∃ A : Subgroup G, (∀ x, x ∈ A ↔ x ∈ Q ∧ InSpan u (D.wc x)) ∧ IsElemAbelian 2 A ∧
      Nat.card A = 16 ∧ H ≤ Subgroup.normalizer (A : Set G) := by
  classical
  let A : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ InSpan u (D.wc x)}
      one_mem' := ⟨Q.one_mem, by rw [D.wc_one]; exact inSpan_zero u⟩
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
        rw [D.wc_mul _ ha.1 _ hb.1]; exact inSpan_xor ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [D.wc_inv ha.1]; exact ha.2⟩ }
  have hA : ∀ x, x ∈ A ↔ x ∈ Q ∧ InSpan u (D.wc x) := fun x => Iff.rfl
  have hel' : ∀ x ∈ A, x * x = 1 ∧ ∀ y ∈ A, x * y = y * x := fun x hx =>
    ⟨(hpre.1 x hx.1 x hx.1 hx.2 hx.2).2, fun y hy => (hpre.1 x hx.1 y hy.1 hx.2 hy.2).1⟩
  refine ⟨A, hA, ⟨⟨⟨fun a b => Subtype.ext ((hel' a.1 a.2).2 b.1 b.2)⟩⟩, fun x hx => ?_⟩, ?_, ?_⟩
  · rw [pow_two]
    exact (hel' x hx).1
  · have e : Nat.card ↥A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
    rw [e]
    exact hpre.2
  · intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ h ∈ H, ∀ x, x ∈ A → h * x * h⁻¹ ∈ A := by
      intro h hh x hx
      obtain ⟨hxQ, hxN⟩ := (hA x).1 hx
      exact (hA _).2 ⟨D.hQn h hh x hxQ, hH h hh x hxQ hxN⟩
    intro x
    constructor
    · exact key h hh x
    · intro hx
      have := key h⁻¹ (H.inv_mem hh) _ hx
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      rwa [e] at this

theorem ab_span (D : FrData H Q (Phi' Q) 6) {z : G} (hzΦ : z ∈ Phi' Q)
    (hΦ : ∀ r ∈ Phi' Q, r = 1 ∨ r = z) {v : Fin 3 → ℕ} (hu : Basis3 u)
    (hint : ∀ x, InSpan u x → InSpan v x → x = 0)
    (hcov : ∀ c < 2 ^ 6, ∃ x, InSpan u x ∧ InSpan v (x ^^^ c))
    (hinvu : SpanInv D.rho.range u) (hinvv : SpanInv D.rho.range v)
    (hpu : PreFacts Q D.wc u) (hpv : PreFacts Q D.wc v) :
    ∃ A B : Subgroup G, IsElemAbelian 2 A ∧ IsElemAbelian 2 B ∧ Nat.card A = 16 ∧
      Nat.card B = 16 ∧ A ⊔ B = Q ∧ A ⊓ B = Subgroup.zpowers z ∧
      H ≤ Subgroup.normalizer (A : Set G) ∧ H ≤ Subgroup.normalizer (B : Set G) := by
  classical
  have hconj : ∀ {w : Fin 3 → ℕ}, SpanInv D.rho.range w → ∀ h ∈ H, ∀ x ∈ Q,
      InSpan w (D.wc x) → InSpan w (D.wc (h * x * h⁻¹)) := by
    intro w hw h hh x hx hxs
    rw [← D.rho_of_mem ⟨h, hh⟩ hx]
    exact hw _ ⟨⟨h, hh⟩, rfl⟩ _ (D.wc_lt x hx) hxs
  obtain ⟨A, hA, hAab, hAc, hAn⟩ := sub_span D hpu (hconj hinvu)
  obtain ⟨B, hB, hBab, hBc, hBn⟩ := sub_span D hpv (hconj hinvv)
  have hz0 : D.wc z = 0 := (D.wc_ker z (Phi'_le Q hzΦ)).2 hzΦ
  have hzA : z ∈ A := (hA z).2 ⟨Phi'_le Q hzΦ, by rw [hz0]; exact inSpan_zero u⟩
  have hzB : z ∈ B := (hB z).2 ⟨Phi'_le Q hzΦ, by rw [hz0]; exact inSpan_zero v⟩
  refine ⟨A, B, hAab, hBab, hAc, hBc, ?_, ?_, hAn, hBn⟩
  · apply _root_.le_antisymm
    · exact sup_le (fun x hx => ((hA x).1 hx).1) (fun x hx => ((hB x).1 hx).1)
    · intro x hx
      have hxlt : D.wc x < 2 ^ 6 := D.wc_lt x hx
      obtain ⟨y, hyu, hyv⟩ := hcov (D.wc x) hxlt
      obtain ⟨e, rfl⟩ := hyu
      have hy64 := comb_lt hu.1 e
      obtain ⟨xa, hxaQ, hxa⟩ := D.wc_surj (comb u e) hy64
      obtain ⟨xb, hxbQ, hxb⟩ := D.wc_surj (comb u e ^^^ D.wc x) (Nat.xor_lt_two_pow hy64 hxlt)
      have hxaA : xa ∈ A := (hA xa).2 ⟨hxaQ, by rw [hxa]; exact ⟨e, rfl⟩⟩
      have hxbB : xb ∈ B := (hB xb).2 ⟨hxbQ, by rw [hxb]; exact hyv⟩
      have hy : x * (xa * xb)⁻¹ ∈ Phi' Q := by
        rw [← D.wc_ker _ (Q.mul_mem hx (Q.inv_mem (Q.mul_mem hxaQ hxbQ))),
          D.wc_mul _ hx _ (Q.inv_mem (Q.mul_mem hxaQ hxbQ)), D.wc_inv (Q.mul_mem hxaQ hxbQ),
          D.wc_mul _ hxaQ _ hxbQ, hxa, hxb, ← Nat.xor_assoc (comb u e), Nat.xor_self,
          Nat.zero_xor, Nat.xor_self]
      have hyA : x * (xa * xb)⁻¹ ∈ A := by
        rcases hΦ _ hy with h | h
        · rw [h]; exact A.one_mem
        · rw [h]; exact hzA
      have hmem : x * (xa * xb)⁻¹ * xa * xb ∈ A ⊔ B :=
        (A ⊔ B).mul_mem ((le_sup_left : A ≤ A ⊔ B) (A.mul_mem hyA hxaA))
          ((le_sup_right : B ≤ A ⊔ B) hxbB)
      have e : x * (xa * xb)⁻¹ * xa * xb = x := by group
      rwa [e] at hmem
  · apply _root_.le_antisymm
    · intro x hx
      obtain ⟨hxQ, hxN1⟩ := (hA x).1 hx.1
      obtain ⟨-, hxN2⟩ := (hB x).1 hx.2
      have hxΦ : x ∈ Phi' Q := (D.wc_ker x hxQ).1 (hint _ hxN1 hxN2)
      rcases hΦ x hxΦ with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    · rw [Subgroup.zpowers_le]
      exact ⟨hzA, hzB⟩

noncomputable def frOf {w : G → ℕ} {d : ℕ} (hcod : CodQ Q w d) (hQH : Q ≤ H)
    (hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q) : FrData H Q (Phi' Q) d where
  wc := w
  hQH := hQH
  hNQ := Phi'_le Q
  hQn := hQn
  hNn := Phi'_normal hQn
  hcomm := fun _ ha _ hb => comm_mem_Phi' ha hb
  wc_lt := hcod.1
  wc_mul := hcod.2.1
  wc_surj := hcod.2.2.1
  wc_ker := hcod.2.2.2

end Hom

end Fct

open Fct

section Main

variable {G : Type} [Group G] [Finite G]

theorem model_main_facts {V M M₀ : Subgroup G} [IsMulCommutative ↥V] {Γ : List B6} {z : G}
    (SP : SplitHyp V M M₀) (C : Coding ↥V) (hΓ1 : ∀ a ∈ autOn M V, C.cB a ∈ Γ)
    (hΓ2 : ∀ B ∈ Γ, ∃ a ∈ autOn M V, C.cB a = B) (hz : z ∈ V) (hzc : C.cd ⟨z, hz⟩ = 5)
    (hF : ModelFacts1277 Γ) (hVel : IsElemAbelian 2 V) (hV64 : Nat.card V = 64)
    {Q : Subgroup G} (hQeq : Q = pCoreOf 2 (Gz z)) (hzQ : z ∈ Q) (hQK : Q ≤ M ⊓ Gz z)
    (hQn : ∀ h ∈ Gz z, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q) (hQ2 : IsPGroup 2 ↥Q)
    (hQmax : ∀ X : Subgroup G, X ≤ Gz z → (∀ h ∈ Gz z, ∀ x ∈ X, h * x * h⁻¹ ∈ X) →
      IsPGroup 2 ↥X → X ≤ Q)
    (hC : ∀ h ∈ Gz z, (∀ x ∈ Q, h * x = x * h) → h ∈ Q)
    (hodd : ¬ 2 ∣ (M ⊓ Gz z).relIndex (Gz z)) (hne : ¬ Gz z ≤ M)
    (hHK : ∀ h ∈ Gz z, h ∈ Subgroup.normalizer (V : Set G) → h ∈ M ⊓ Gz z) :
    StructAt G z := by
  classical
  obtain ⟨hnd, hall⟩ := hF
  have hκ : KCod (M ⊓ Gz z) (mkTab (stabL Γ 5)) (kap (mkTab (stabL Γ 5)) C SP) :=
    kCod_of_split SP C hΓ1 hΓ2 hz hzc hnd
  have hkapV : ∀ v (hv : v ∈ V),
      kap (mkTab (stabL Γ 5)) C SP v = (mkTab (stabL Γ 5)).idB * 64 + C.cd ⟨v, hv⟩ := by
    intro v hv
    unfold kap
    rw [bpart_V C SP hv, cpart_V C SP hv]
    rfl
  have hzK : z ∈ M ⊓ Gz z :=
    Subgroup.mem_inf.2 ⟨SP.hVM hz, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hκz : kap (mkTab (stabL Γ 5)) C SP z = (mkTab (stabL Γ 5)).idB * 64 + 5 := by
    rw [hkapV z hz, hzc]
  have hzH : ∀ h ∈ Gz z, h * z * h⁻¹ = z := fun h hh => by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hh
  have hKH : M ⊓ Gz z ≤ Gz z := inf_le_right
  have hm : (M ⊓ Gz z).relIndex (Gz z) * Nat.card ↥(M ⊓ Gz z) = Nat.card ↥(Gz z) := by
    have := Subgroup.relIndex_mul_card (H := M ⊓ Gz z) (K := Gz z)
    rwa [inf_eq_left.2 hKH] at this
  have hm1 : (M ⊓ Gz z).relIndex (Gz z) ≠ 1 := fun h1 =>
    hne ((Subgroup.relIndex_eq_one.1 h1).trans inf_le_left)
  have hNfr := Phi'_frattini hQ2
  rcases hall (H := Gz z) hκ hKH hQK hQn hQ2 hQmax hC hzH hzK hκz with
    hV | hNF | hNC | hSig | hSurv
  ·
    exfalso
    obtain ⟨hVc, bp, hbp, -, hlen, hfix, hpair⟩ := hV
    have hVK : V ≤ M ⊓ Gz z := fun v hv => Subgroup.mem_inf.2 ⟨SP.hVM hv,
      Subgroup.mem_centralizer_singleton_iff.2 (comm_of_isElemAbelian hVel hv hz)⟩
    have hVQ : V ≤ Q := by
      intro v hv
      obtain ⟨q, hq, hqv⟩ := hVc (C.cd ⟨v, hv⟩) (C.cd_lt _)
      have := hκ.inj q (hQK hq) v (hVK hv) (hqv.trans (hkapV v hv).symm)
      rw [← this]
      exact hq
    have hnorm : ∀ h ∈ Gz z, h ∈ Subgroup.normalizer (V : Set G) := by
      intro h hh
      have hE : cjS h V ≤ Q := by
        intro y hy
        have hy' : h⁻¹ * y * h ∈ V := mem_cjS_iff.1 hy
        have := hQn h hh _ (hVQ hy')
        have e : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
        rwa [e] at this
      have hEM : cjS h V ≤ Subgroup.normalizer (V : Set G) :=
        hE.trans (hQK.trans (inf_le_left.trans SP.hMV))
      have hbs : ∀ e (he : e ∈ cjS h V),
          C.cB (conjAct V ⟨e, hEM he⟩) ∈ bp.map ((stabL Γ 5).getD · B6.id) := by
        intro e he
        have heK : e ∈ M ⊓ Gz z := hQK (hE he)
        have heM : e ∈ M := (Subgroup.mem_inf.1 heK).1
        have hbG0 : bpart C SP e ∈ stabL Γ 5 := bpart_mem_stabL SP C hΓ1 hz hzc heK
        have hdiv : kap (mkTab (stabL Γ 5)) C SP e / 64 = (stabL Γ 5).idxOf (bpart C SP e) := by
          unfold kap
          have := cpart_lt C SP e
          change ((stabL Γ 5).idxOf (bpart C SP e) * 64 + cpart C SP e) / 64 = _
          omega
        have hbp' : bpart C SP e = C.cB (conjAct V ⟨e, hEM he⟩) := by
          rw [bpart_of_mem C SP heM]; rfl
        refine List.mem_map.2 ⟨kap (mkTab (stabL Γ 5)) C SP e / 64, hbp _ (hE he), ?_⟩
        rw [hdiv]
        change (stabL Γ 5).getD ((stabL Γ 5).idxOf (bpart C SP e)) B6.id = _
        rw [getD_idxOf hbG0, hbp']
      have hle : cjS h V ≤ V :=
        census_real C SP.hCV (isElemAbelian_cjS hVel) (by rw [card_cjS, hV64]) hEM hbs hlen hfix
          hpair
      have heq : cjS h V = V := Subgroup.eq_of_le_of_card_ge hle (by rw [card_cjS])
      exact mem_normalizer_of_cjS_eq heq
    exact hne fun h hh => (Subgroup.mem_inf.1 (hHK h hh (hnorm h hh))).1
  ·
    obtain ⟨k, hk, hkQ, htriv⟩ := hNF
    exact (hkQ (mem_of_trivial_action hQmax (hQK.trans hKH) hQn hQ2 hC (Phi'_le Q)
      (Phi'_normal hQn) hNfr (hKH hk) htriv)).elim
  ·
    rcases hNC with h | ⟨x, hx, hxQ, hxc⟩
    · exact (h hzQ).elim
    · exact (hxQ (hC x (hKH hx) hxc)).elim
  ·
    exfalso
    obtain ⟨d, w, φ, b, k, hcod, hlab, hcard, hbr⟩ := hSig
    let D : FrData (Gz z) Q (Phi' Q) d := frOf hcod (hQK.trans hKH) hQn
    have hR : D.rho.range ≤ Sig d φ :=
      D.range_le_Sig φ (fun x => φ (w x)) (fun x _ => rfl) fun h hh x hx => hlab h hh x hx
    have hcardH : Nat.card ↥(Gz z) = Nat.card Q * Nat.card D.rho.range :=
      D.card_H hQmax hQ2 hC hNfr
    obtain ⟨e, he⟩ : Nat.card Q ∣ Nat.card ↥(M ⊓ Gz z) := Subgroup.card_dvd_of_le hQK
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have hKpos : 0 < Nat.card ↥(M ⊓ Gz z) := Nat.card_pos
    have hediv : Nat.card ↥(M ⊓ Gz z) / Nat.card Q = e := by
      rw [he, Nat.mul_div_cancel_left _ hQpos]
    rw [hediv] at hcard
    have hepos : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at he
        omega
      · exact h0
    set mi := (M ⊓ Gz z).relIndex (Gz z) with hmdef
    have hR_eq : Nat.card D.rho.range = mi * e := by
      apply Nat.eq_of_mul_eq_mul_left hQpos
      rw [← hcardH, ← hm, he]
      ring
    have hdvd : mi * e ∣ e * (b * 2 ^ k) := by
      rw [← hcard, ← hR_eq]
      exact Subgroup.card_dvd_of_le hR
    have hmdiv : mi ∣ b * 2 ^ k := by
      rw [mul_comm mi e] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left hepos hdvd
    have hcop : Nat.Coprime mi (2 ^ k) := Nat.Coprime.pow_right k
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd))
    have hmb : mi ∣ b := hcop.dvd_of_dvd_mul_right hmdiv
    rcases hbr with ⟨rfl, O, hOK, hOn, hO2, hOc⟩ | ⟨rfl, hbk, X, hXS, hXn, hX2, hX8⟩
    ·
      have hm3 : mi = 3 := ((Nat.dvd_prime Nat.prime_three).1 hmb).resolve_left hm1
      refine no_index_three hKH hm3 hOK hOn hO2 ?_
      rw [← hQeq]
      exact hOc
    ·
      have hm7 : mi = 7 := ((Nat.dvd_prime (by norm_num)).1 hmb).resolve_left hm1
      have hYn : ∀ r ∈ D.rho.range, ∀ y ∈ X ⊓ D.rho.range, r * y * r⁻¹ ∈ X ⊓ D.rho.range := by
        intro r hr y hy
        exact ⟨hXn r (hR hr) y hy.1, D.rho.range.mul_mem (D.rho.range.mul_mem hr hy.2)
          (D.rho.range.inv_mem hr)⟩
      have hbot : X ⊓ D.rho.range = ⊥ :=
        D.eq_bot_of_normal_two hQmax hQ2 hC hNfr inf_le_right hYn (hX2.to_le inf_le_left)
      have hle := card_le_relIndex_of_inf_eq_bot hXS hR hbot
      have hrel := Subgroup.relIndex_mul_card (H := D.rho.range) (K := Sig d φ)
      rw [inf_eq_left.2 hR, hcard, hR_eq, hm7] at hrel
      have h2 : D.rho.range.relIndex (Sig d φ) * (7 * e) = 2 ^ k * (7 * e) := by
        rw [hrel]; ring
      have h3 := Nat.eq_of_mul_eq_mul_right (by omega) h2
      have h4 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  ·
    obtain ⟨w, φ, hcod, hlab, hQc, hzΦ, hΦ, hz1, hcen, hcm, himg⟩ := hSurv
    let D : FrData (Gz z) Q (Phi' Q) 6 := frOf hcod (hQK.trans hKH) hQn
    have hR : D.rho.range ≤ Sig 6 φ :=
      D.range_le_Sig φ (fun x => φ (w x)) (fun x _ => rfl) fun h hh x hx => hlab h hh x hx
    have hcardH : Nat.card ↥(Gz z) = Nat.card Q * Nat.card D.rho.range :=
      D.card_H hQmax hQ2 hC hNfr
    obtain ⟨h168, u, v, hbu, -, hint, hcov, hinvu, hinvv, hker, hpu, hpv⟩ :=
      himg D (fun x => rfl) _ (by rw [← hcardH, ← hm]; ring) hodd hm1
    obtain ⟨f, hfs, hfk⟩ := sl_hom_span D hR hQmax hQ2 hC hbu hinvu hker h168
    obtain ⟨A, B, hAab, hBab, hAc, hBc, hABQ, hABz, hAn, hBn⟩ :=
      ab_span D hzΦ hΦ hbu hint hcov hinvu hinvv hpu hpv
    have hext := CFSG.KS.S1277Vl.extraspecial_of hQ2 D hzΦ hΦ hz1 hcen hcm fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.1 (hKH (hQK hq))
    subst hQeq
    refine ⟨hext, by rw [hQc]; norm_num, ?_, ⟨f, hfs, hfk⟩, A, B, hAab, hBab, hAc, hBc, hABQ,
      hABz, hAn, hBn⟩
    intro x hx
    exact hC x hx.1 (fun y hy => ((Subgroup.mem_centralizer_iff.1 hx.2) y hy).symm)

end Main

end CFSG.Quasithin.H13.I1277

end
