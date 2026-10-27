module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KCoord
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def NQ (Q : Subgroup G) (d : G) : Subgroup G :=
  Subgroup.normalizer (Q : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)

theorem NQ_conj_d {Q : Subgroup G} {d g : G} (hg : g ∈ NQ Q d) :
    g * d * g⁻¹ ∈ Subgroup.zpowers d :=
  (Subgroup.mem_normalizer_iff.mp hg.2 d).mp (Subgroup.mem_zpowers d)

theorem Q_le_NQ {Q : Subgroup G} {d : G} (hdc : ∀ q ∈ Q, q * d * q⁻¹ = d) : Q ≤ NQ Q d := by
  intro q hq
  have hcomm : q * d = d * q := by
    calc q * d = q * d * q⁻¹ * q := by group
      _ = d * q := by rw [hdc q hq]
  have hqz : ∀ z ∈ Subgroup.zpowers d, q * z * q⁻¹ = z := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute q (d ^ k) := (Commute.zpow_right (show Commute q d from hcomm) k)
    rw [hc.eq]; group
  refine ⟨Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => Q.mul_mem (Q.mul_mem hq hx)
    (Q.inv_mem hq), fun hx => ?_⟩, Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_,
    fun hx => ?_⟩⟩
  · have := Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hx) hq
    simpa [mul_assoc] using this
  · rw [hqz x hx]; exact hx
  · have e : q * (q * x * q⁻¹) * q⁻¹ = q * x * q⁻¹ := hqz _ hx
    have e2 : q * x * q⁻¹ = x := by
      calc q * x * q⁻¹ = q⁻¹ * (q * (q * x * q⁻¹) * q⁻¹) * q := by group
        _ = q⁻¹ * (q * x * q⁻¹) * q := by rw [e]
        _ = x := by group
    rw [e2] at hx
    exact hx

theorem isPGroup_zpowers_of_pow {g : G} {n : ℕ} (h : g ^ (3 ^ n) = 1) :
    IsPGroup 3 (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h
  apply IsPGroup.of_card_dvd_pow (n := n)
  rw [Nat.card_zpowers]; exact hd

namespace SympBasis

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (h : SympBasis A Q d a₀ a₁ f₀ f₁)

include h

@[expose] noncomputable def MgHom : NQ Q d →* M4 where
  toFun g := Mg d a₀ a₁ f₀ f₁ g
  map_one' := h.Mg_one
  map_mul' g g' := h.Mg_mul g.2.1 (NQ_conj_d g.2) g'.2.1

theorem mem_Q_of_Mg_one {g : G} (hg : g ∈ NQ Q d) (hM : Mg d a₀ a₁ f₀ f₁ g = 1) {n : ℕ}
    (hn : g ^ (3 ^ n) = 1) : g ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have hbQ := h.hAQ hb
    have h1 := h.Mg_apply hg.1 (NQ_conj_d hg) hbQ
    rw [hM, Matrix.one_mulVec] at h1
    have hz := h.Phi_eq hbQ (h.conj_mem hg.1 hbQ) h1.symm
    have : g * b * g⁻¹ = b * (b⁻¹ * (g * b * g⁻¹)) := by group
    rw [this]
    exact A.mul_mem hb (Subgroup.zpowers_le.mpr h.hdA hz)
  have hS3 : IsPGroup 3 (Subgroup.zpowers g ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow hn) h.hQS.isPGroup
      (Subgroup.zpowers_le.mpr hg.1)
  have hSA : (Subgroup.zpowers g ⊔ Q : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hgA) h.hQS.le
  have heq := h.hQS.eq_of_le (le_sup_right : Q ≤ Subgroup.zpowers g ⊔ Q) hSA hS3
  rw [← heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g)

theorem exists_three_elt {g : G} (hg : g ∈ NQ Q d) (h3 : (Mg d a₀ a₁ f₀ f₁ g) ^ 3 = 1) :
    ∃ g' ∈ NQ Q d, (∃ n, g' ^ (3 ^ n) = 1) ∧
      Mg d a₀ a₁ f₀ f₁ g' = Mg d a₀ a₁ f₀ f₁ g := by
  have hord : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord 3 (by norm_num)
  refine ⟨g ^ (m * m), Subgroup.pow_mem _ hg _, ⟨e, ?_⟩, ?_⟩
  · calc (g ^ (m * m)) ^ (3 ^ e) = (g ^ (3 ^ e * m)) ^ m := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ = 1 := by rw [← hn, pow_orderOf_eq_one, one_pow]
  · have hmm : m * m % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
    obtain ⟨q, hq⟩ : ∃ q, m * m = 3 * q + 1 := ⟨m * m / 3, by omega⟩
    have hpow : Mg d a₀ a₁ f₀ f₁ (g ^ (m * m)) = (Mg d a₀ a₁ f₀ f₁ g) ^ (m * m) :=
      map_pow h.MgHom (⟨g, hg⟩ : NQ Q d) (m * m)
    rw [hpow, hq, pow_succ, pow_mul, h3, one_pow, one_mul]

end SympBasis

theorem exists_dual : ∀ u : V4, u ≠ 0 → ∀ c : F3, ∃ w : V4, omega4 w u = c := by
  decide +kernel

namespace SympBasis

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (h : SympBasis A Q d a₀ a₁ f₀ f₁)

include h

theorem exists_cm {f z : G} (hfQ : f ∈ Q) (hfd : f ∉ Subgroup.zpowers d)
    (hz : z ∈ Subgroup.zpowers d) : ∃ q ∈ Q, cm q f = z := by
  have hC := h.hC
  have hPf : Phi d a₀ a₁ f₀ f₁ f ≠ 0 := fun h0 => hfd (h.Phi_ker hfQ h0)
  obtain ⟨w, hw⟩ := exists_dual _ hPf (dl d z)
  refine ⟨rep d a₀ a₁ f₀ f₁ w, h.rep_mem w, ?_⟩
  have h1 : om d (rep d a₀ a₁ f₀ f₁ w) f = dl d z := by
    rw [← h.omega4_Phi (h.rep_mem w) hfQ, h.Phi_rep]; exact hw
  have hmem := hC.hcm f hfQ _ (h.rep_mem w)
  have e1 := dl_zpow_val hC.hd3 hC.hd1 hmem
  have e2 := dl_zpow_val hC.hd3 hC.hd1 hz
  unfold om at h1
  rw [← e1, ← e2, h1]

theorem no_fix3 {f g : G} (hfQ : f ∈ Q) (hfd : f ∉ Subgroup.zpowers d)
    (hbound : ∀ R : Subgroup G, IsPGroup 3 R → R ≤ Subgroup.centralizer ({f} : Set G) →
      Nat.card R ≤ 81)
    (hg : g ∈ NQ Q d) (hg3 : ∃ n, g ^ (3 ^ n) = 1)
    (hfix : (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ f) = Phi d a₀ a₁ f₀ f₁ f) :
    g ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC := h.hC
  by_contra hgQ
  obtain ⟨n, hn⟩ := hg3
  have hz : f⁻¹ * (g * f * g⁻¹) ∈ Subgroup.zpowers d :=
    h.Phi_eq hfQ (h.conj_mem hg.1 hfQ) (by rw [h.Mg_apply hg.1 (NQ_conj_d hg) hfQ, hfix])
  obtain ⟨q, hqQ, hqcm⟩ := h.exists_cm hfQ hfd (Subgroup.inv_mem _ hz)
  set z := f⁻¹ * (g * f * g⁻¹) with hzdef
  have hgf : g * f * g⁻¹ = f * z := by rw [hzdef]; group
  have hqf : q * f * q⁻¹ = f * z⁻¹ := by
    have : q * f * q⁻¹ = f * cm q f := by unfold cm; group
    rw [this, hqcm]
  have hqz : q * z * q⁻¹ = z := by
    have := hC.hzc z hz q hqQ
    rw [this]; group
  have hqNQ : q ∈ NQ Q d := Q_le_NQ h.hdc hqQ
  set g' := q * g with hg'def
  have hg'NQ : g' ∈ NQ Q d := (NQ Q d).mul_mem hqNQ hg
  have hg'f : g' * f * g'⁻¹ = f := by
    calc g' * f * g'⁻¹ = q * (g * f * g⁻¹) * q⁻¹ := by rw [hg'def]; group
      _ = q * (f * z) * q⁻¹ := by rw [hgf]
      _ = (q * f * q⁻¹) * (q * z * q⁻¹) := by group
      _ = (f * z⁻¹) * z := by rw [hqf, hqz]
      _ = f := by group
  have hS3 : IsPGroup 3 (Subgroup.zpowers g ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow hn) h.hQS.isPGroup
      (Subgroup.zpowers_le.mpr hg.1)
  have hg'S : g' ∈ (Subgroup.zpowers g ⊔ Q : Subgroup G) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right hqQ) (Subgroup.mem_sup_left (Subgroup.mem_zpowers g))
  have hg'Q : g' ∉ Q := by
    intro hQ'
    apply hgQ
    have : g = q⁻¹ * g' := by rw [hg'def]; group
    rw [this]
    exact Q.mul_mem (Q.inv_mem hqQ) hQ'
  set H : Subgroup G := (Q ⊓ Subgroup.centralizer ({f} : Set G)) ⊔ Subgroup.zpowers g' with hH
  have hHC : H ≤ Subgroup.centralizer ({f} : Set G) := by
    refine sup_le inf_le_right ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    calc g' * f = (g' * f * g'⁻¹) * g' := by group
      _ = f * g' := by rw [hg'f]
  have hHS : H ≤ (Subgroup.zpowers g ⊔ Q : Subgroup G) := by
    refine sup_le (inf_le_left.trans le_sup_right) ?_
    rw [Subgroup.zpowers_le]; exact hg'S
  have hH81 := hbound H (hS3.to_le hHS) hHC
  have hlt : (Q ⊓ Subgroup.centralizer ({f} : Set G)) < H := by
    refine lt_of_le_of_ne le_sup_left fun heq => hg'Q ?_
    have : g' ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers g')
    rw [← heq] at this
    exact this.1
  have hCQ := Subgroup.card_lt_of_lt hlt
  let lamf : Q →* Multiplicative F3 :=
    { toFun := fun y => Multiplicative.ofAdd (om d y f)
      map_one' := by
        show Multiplicative.ofAdd (om d ((1 : Q) : G) f) = 1
        rw [Subgroup.coe_one, hC.om_one_left]; rfl
      map_mul' := by
        intro y y'
        show Multiplicative.ofAdd (om d ((y * y' : Q) : G) f) =
          Multiplicative.ofAdd (om d y f) * Multiplicative.ofAdd (om d y' f)
        rw [Subgroup.coe_mul, hC.om_add_left y.2 y'.2 hfQ]; rfl }
  have hker : lamf.ker = (Q ⊓ Subgroup.centralizer ({f} : Set G)).subgroupOf Q := by
    ext y
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have : om d y f = 0 := ofAdd_eq_one.mp hy
      exact ⟨y.2, hC.comm_of_om_zero y.2 hfQ this⟩
    · rintro ⟨-, hy⟩
      exact ofAdd_eq_one.mpr (hC.om_zero_of_comm hy)
  have hprod := Subgroup.card_ker_mul_card_range lamf
  have hr3 : Nat.card lamf.range ≤ 3 := by
    have := Subgroup.card_le_card_group lamf.range
    have h3 : Nat.card (Multiplicative F3) = 3 := by
      rw [Nat.card_eq_fintype_card]; decide +kernel
    omega
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, h.hQ243] at hprod
  have h81 : 81 ≤ Nat.card (Q ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := by
    by_contra hlt81
    push Not at hlt81
    have : Nat.card (Q ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) *
        Nat.card lamf.range ≤ 80 * 3 :=
      Nat.mul_le_mul (by omega) hr3
    omega
  omega

theorem MgHom_inv_eq {n p : NQ Q d} (hnp : h.MgHom n = h.MgHom p) :
    h.MgHom n⁻¹ = h.MgHom p⁻¹ := by
  have h1 : h.MgHom n⁻¹ * h.MgHom n = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : h.MgHom p * h.MgHom p⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc h.MgHom n⁻¹ = h.MgHom n⁻¹ * (h.MgHom p * h.MgHom p⁻¹) := by rw [h2, mul_one]
    _ = h.MgHom n⁻¹ * (h.MgHom n * h.MgHom p⁻¹) := by rw [hnp]
    _ = h.MgHom p⁻¹ := by rw [← mul_assoc, h1, one_mul]

theorem Mg_mul_inv {r s : G} (hr : r ∈ NQ Q d) (hs : s ∈ NQ Q d)
    (hrs : Mg d a₀ a₁ f₀ f₁ r = Mg d a₀ a₁ f₀ f₁ s) : Mg d a₀ a₁ f₀ f₁ (r * s⁻¹) = 1 := by
  have e := map_mul h.MgHom (⟨r, hr⟩ : NQ Q d) (⟨s, hs⟩ : NQ Q d)⁻¹
  have e2 : h.MgHom (⟨s, hs⟩ : NQ Q d) * h.MgHom (⟨s, hs⟩ : NQ Q d)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have e3 : h.MgHom (⟨r, hr⟩ : NQ Q d) = h.MgHom ⟨s, hs⟩ := hrs
  rw [e3, e2] at e
  exact e

theorem Mg_inv_mul {r s : G} (hr : r ∈ NQ Q d) (hs : s ∈ NQ Q d)
    (hrs : Mg d a₀ a₁ f₀ f₁ s = Mg d a₀ a₁ f₀ f₁ r) : Mg d a₀ a₁ f₀ f₁ (r⁻¹ * s) = 1 := by
  have e := map_mul h.MgHom (⟨r, hr⟩ : NQ Q d)⁻¹ ⟨s, hs⟩
  have e2 : h.MgHom (⟨r, hr⟩ : NQ Q d)⁻¹ * h.MgHom ⟨r, hr⟩ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have e3 : h.MgHom (⟨s, hs⟩ : NQ Q d) = h.MgHom ⟨r, hr⟩ := hrs
  rw [e3, e2] at e
  exact e

theorem isSylow_of_surj {N₁ R : Subgroup G} (hN₁ : N₁ ≤ NQ Q d) (hR3 : IsPGroup 3 R)
    (hRN : R ≤ N₁) (hQR : Q ≤ R)
    (hsurj : ∀ n ∈ N₁, ∃ r ∈ R, Mg d a₀ a₁ f₀ f₁ n = Mg d a₀ a₁ f₀ f₁ r) : IsSylowOf 3 R N₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS, hRS⟩ := exists_sylowOf_ge hR3 hRN
  have hSR : S ≤ R := by
    intro s hs
    obtain ⟨r, hr, hsr⟩ := hsurj s (hS.le hs)
    have hκ := h.Mg_inv_mul (hN₁ (hRN hr)) (hN₁ (hS.le hs)) hsr
    have hκS : r⁻¹ * s ∈ S := S.mul_mem (S.inv_mem (hRS hr)) hs
    obtain ⟨n, hn⟩ := hS.isPGroup ⟨r⁻¹ * s, hκS⟩
    have hn' : (r⁻¹ * s) ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hκQ := h.mem_Q_of_Mg_one ((NQ Q d).mul_mem ((NQ Q d).inv_mem (hN₁ (hRN hr)))
      (hN₁ (hS.le hs))) hκ hn'
    have : s = r * (r⁻¹ * s) := by group
    rw [this]
    exact R.mul_mem hr (hQR hκQ)
  have : S = R := le_antisymm hSR hRS
  rw [← this]; exact hS

theorem sylow_conj_K {P P' : Subgroup G} (hPN : P ≤ NQ Q d) (hP'N : P' ≤ NQ Q d)
    (hP3 : IsPGroup 3 P) (hP'3 : IsPGroup 3 P') (hQP : Q ≤ P) (hQP' : Q ≤ P')
    (h1 : ∀ p ∈ P, ∃ p' ∈ P', Mg d a₀ a₁ f₀ f₁ p = Mg d a₀ a₁ f₀ f₁ p')
    (h2 : ∀ p' ∈ P', ∃ p ∈ P, Mg d a₀ a₁ f₀ f₁ p' = Mg d a₀ a₁ f₀ f₁ p) :
    ∃ κ ∈ NQ Q d, Mg d a₀ a₁ f₀ f₁ κ = 1 ∧ ∀ y, y ∈ P' ↔ κ⁻¹ * y * κ ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N₁ : Subgroup G :=
    { carrier := {n | ∃ hn : n ∈ NQ Q d, ∃ p ∈ P, Mg d a₀ a₁ f₀ f₁ n = Mg d a₀ a₁ f₀ f₁ p}
      mul_mem' := by
        rintro a b ⟨ha, p, hp, hap⟩ ⟨hb, q, hq, hbq⟩
        refine ⟨(NQ Q d).mul_mem ha hb, p * q, P.mul_mem hp hq, ?_⟩
        have e1 := h.Mg_mul ha.1 (NQ_conj_d ha) hb.1
        have e2 := h.Mg_mul (hPN hp).1 (NQ_conj_d (hPN hp)) (hPN hq).1
        show Mg d a₀ a₁ f₀ f₁ (a * b) = Mg d a₀ a₁ f₀ f₁ (p * q)
        rw [e1, e2, hap, hbq]
      one_mem' := ⟨(NQ Q d).one_mem, 1, P.one_mem, rfl⟩
      inv_mem' := by
        rintro a ⟨ha, p, hp, hap⟩
        refine ⟨(NQ Q d).inv_mem ha, p⁻¹, P.inv_mem hp, ?_⟩
        have := h.MgHom_inv_eq (n := ⟨a, ha⟩) (p := ⟨p, hPN hp⟩) hap
        exact this }
  have hN₁ : N₁ ≤ NQ Q d := fun n hn => hn.1
  have hPN₁ : P ≤ N₁ := fun p hp => ⟨hPN hp, p, hp, rfl⟩
  have hP'N₁ : P' ≤ N₁ := fun p' hp' => by
    obtain ⟨p, hp, hpp⟩ := h2 p' hp'
    exact ⟨hP'N hp', p, hp, hpp⟩
  have hSylP : IsSylowOf 3 P N₁ := h.isSylow_of_surj hN₁ hP3 hPN₁ hQP
    (fun n hn => hn.2)
  have hSylP' : IsSylowOf 3 P' N₁ := h.isSylow_of_surj hN₁ hP'3 hP'N₁ hQP'
    (fun n hn => by
      obtain ⟨-, p, hp, hnp⟩ := hn
      obtain ⟨p', hp', hpp'⟩ := h1 p hp
      exact ⟨p', hp', hnp.trans hpp'⟩)
  obtain ⟨n, hnN, hn⟩ := hSylP.exists_mem_conj hSylP'
  obtain ⟨hnNQ, p, hp, hnp⟩ := hnN
  refine ⟨n * p⁻¹, (NQ Q d).mul_mem hnNQ ((NQ Q d).inv_mem (hPN hp)), ?_, ?_⟩
  · exact h.Mg_mul_inv hnNQ (hPN hp) hnp
  · intro y
    rw [hn y]
    have e : (n * p⁻¹)⁻¹ * y * (n * p⁻¹) = p * (n⁻¹ * y * n) * p⁻¹ := by group
    rw [e]
    constructor
    · intro hy
      exact P.mul_mem (P.mul_mem hp hy) (P.inv_mem hp)
    · intro hy
      have := P.mul_mem (P.mul_mem (P.inv_mem hp) hy) hp
      simpa [mul_assoc] using this

end SympBasis

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
