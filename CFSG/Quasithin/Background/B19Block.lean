module

public import CFSG.Quasithin.Background.B19Basic
public import CFSG.Quasithin.Background.B1NaturalL2

public section

namespace CFSG.Quasithin.B19

open CFSG.Quasithin
open scoped commutatorElement

variable {V : Type*} [CommGroup V]

structure TvBlock (Φ : Subgroup (MulAut V)) (t x : MulAut V) (w : V) : Prop where
  tw : IsTransvectionWith t w
  t1 : t ≠ 1
  mem : x ∈ Φ
  x1 : x ≠ 1
  x3 : x ^ 3 = 1
  inv : t * x * t⁻¹ = x⁻¹
  comm_eq : ⁅Φ, Subgroup.zpowers t⁆ = Subgroup.zpowers x
  card_comm : Nat.card (commV (Subgroup.zpowers x)) = 4
  w_mem : w ∈ commV (Subgroup.zpowers x)
  fix : ∀ c ∈ fixV (Subgroup.zpowers x), t c = c
  central : ∀ g ∈ Φ, g * x = x * g
  inverted : ∀ y ∈ Φ, t * y * t⁻¹ = y⁻¹ → y ∈ Subgroup.zpowers x
  card_G : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) = 6
  faithful : (Subgroup.zpowers x ⊔ Subgroup.zpowers t) ⊓ centSub (commV (Subgroup.zpowers x)) = ⊥
  full : autSub (Subgroup.zpowers x ⊔ Subgroup.zpowers t) (commV (Subgroup.zpowers x)) = ⊤
  iso : Nonempty (↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) ≃*
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))

theorem exists_tvBlock [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Φ : Subgroup (MulAut V)}
    (hΦodd : Odd (Nat.card Φ)) [Group.IsSolvable Φ] {t : MulAut V} {w : V}
    (htw : IsTransvectionWith t w) (ht1 : t ≠ 1)
    (htΦ : ∀ f ∈ Φ, t * f * t⁻¹ ∈ Φ) (hnt : ∃ f ∈ Φ, f * t ≠ t * f) :
    ∃ x, TvBlock Φ t x w := by
  classical
  have hsq : t * t = 1 := B1.tv_sq hV htw ht1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
  set H := Φ ⊔ Subgroup.zpowers t with hHdef
  have htH : t ∈ H := (le_sup_right : Subgroup.zpowers t ≤ H) (Subgroup.mem_zpowers t)
  have hΦH : Φ ≤ H := le_sup_left
  have hmem : ∀ h ∈ H, h ∈ Φ ∨ h * t ∈ Φ := fun h hh => mem_or_mul_mem_of_mem_sup hsq htΦ hh
  have hHΦ : ∀ h ∈ H, ∀ f ∈ Φ, h * f * h⁻¹ ∈ Φ := by
    intro h hh f hf
    rcases hmem h hh with h1 | h1
    · exact Φ.mul_mem (Φ.mul_mem h1 hf) (Φ.inv_mem h1)
    · have e : h * f * h⁻¹ = (h * t) * (t * f * t⁻¹) * (h * t)⁻¹ := by
        have : t * f * t⁻¹ = t⁻¹ * f * t := by rw [htinv]
        rw [this]
        group
      rw [e]
      exact Φ.mul_mem (Φ.mul_mem h1 (htΦ f hf)) (Φ.inv_mem h1)
  have hsolv : Group.IsSolvable ↥H := isSolvable_sup_zpowers Φ hsq htΦ
  have hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ H → (Q.subgroupOf H).Normal → IsPGroup 2 Q →
      Q = ⊥ := by
    intro Q hQH hQn hQp
    have hQΦ : ∀ y ∈ Q, y ∈ Φ → y = 1 := fun y hyQ hyΦ =>
      eq_one_of_isPGroup_of_odd hQp hΦodd hyQ hyΦ
    have hQconj : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
      intro h hh q hq
      have := hQn.conj_mem ⟨q, hQH hq⟩ hq ⟨h, hh⟩
      exact this
    by_contra hne
    obtain ⟨⟨q, hqQ⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hqH : q ∈ H := hQH hqQ
    have hqΦ : q ∉ Φ := fun h => hq1' (hQΦ q hqQ h)
    have hqt : q * t ∈ Φ := (hmem q hqH).resolve_left hqΦ
    have hcomm : ∀ f ∈ Φ, f * q = q * f := by
      intro f hf
      have h1 : f * q * f⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hQconj f (hΦH hf) q hqQ) (Q.inv_mem hqQ)
      have h2 : f * q * f⁻¹ * q⁻¹ ∈ Φ := by
        have e : f * q * f⁻¹ * q⁻¹ = f * (q * f⁻¹ * q⁻¹) := by group
        rw [e]
        exact Φ.mul_mem hf (hHΦ q hqH _ (Φ.inv_mem hf))
      have h3 := hQΦ _ h1 h2
      calc f * q = f * q * f⁻¹ * q⁻¹ * (q * f) := by group
        _ = q * f := by rw [h3, one_mul]
    have hq2 : q * q = 1 := by
      refine hQΦ _ (Q.mul_mem hqQ hqQ) ?_
      have e : q * q = (q * t) * (t * (q * t) * t⁻¹) := by
        calc q * q = q * (t * t) * q := by rw [hsq, mul_one]
          _ = (q * t) * (t * (q * t) * t⁻¹) := by group
      rw [e]
      exact Φ.mul_mem hqt (htΦ _ hqt)
    have hqtq : q * t * q = t := by
      calc q * t * q = q * (q * t) := hcomm _ hqt
        _ = (q * q) * t := by group
        _ = t := by rw [hq2, one_mul]
    have hf2 : (q * t) * (q * t) = 1 := by
      calc (q * t) * (q * t) = (q * t * q) * t := by group
        _ = 1 := by rw [hqtq, hsq]
    have hqt1 : q * t = 1 := eq_one_of_sq_of_odd hΦodd hqt hf2
    have htq : t = q⁻¹ := eq_inv_of_mul_eq_one_right hqt1
    obtain ⟨f, hf, hft⟩ := hnt
    apply hft
    rw [htq]
    calc f * q⁻¹ = q⁻¹ * (q * f) * q⁻¹ := by group
      _ = q⁻¹ * (f * q) * q⁻¹ := by rw [hcomm f hf]
      _ = q⁻¹ * f := by group
  have hJX := B1.closure_transvectionsIn_le H
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn H)) :=
    B1.solvable_of_le hJX hsolv
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO2
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn H))) =
      Subgroup.closure (transvectionsIn H) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun s hs => hs.1
    · exact Subgroup.closure_mono fun s hs => ⟨Subgroup.subset_closure hs, hs.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hV hsolvJ hOJ hcl
  have htJ : t ∈ transvectionsIn (Subgroup.closure (transvectionsIn H)) :=
    ⟨Subgroup.subset_closure ⟨htH, ht1, w, htw⟩, ht1, w, htw⟩
  obtain ⟨H₁, hH₁, htH₁⟩ := hb.cover t htJ
  have hconjH₁ : ∀ f ∈ Φ, f * t * f⁻¹ ∈ H₁ := by
    intro f hf
    have hs : f * t * f⁻¹ ∈ transvectionsIn (Subgroup.closure (transvectionsIn H)) := by
      have hsH : f * t * f⁻¹ ∈ H := H.mul_mem (H.mul_mem (hΦH hf) htH) (H.inv_mem (hΦH hf))
      have hstr : IsTransvection (f * t * f⁻¹) := B1.isTransvection_conj ⟨ht1, w, htw⟩ f
      exact ⟨Subgroup.subset_closure ⟨hsH, hstr⟩, hstr⟩
    obtain ⟨H₂, hH₂, hsH₂⟩ := hb.cover _ hs
    by_contra hnot
    have hne : H₁ ≠ H₂ := fun h => hnot (h ▸ hsH₂)
    have hts : t * (f * t * f⁻¹) = (f * t * f⁻¹) * t := hb.comm H₁ hH₁ H₂ hH₂ hne t htH₁ _ hsH₂
    have hneq : t ≠ f * t * f⁻¹ := fun h => hnot (h ▸ htH₁)
    have huΦ : t * (f * t * f⁻¹) ∈ Φ := by
      have e : t * (f * t * f⁻¹) = (t * f * t⁻¹) * f⁻¹ := by rw [htinv]; group
      rw [e]
      exact Φ.mul_mem (htΦ f hf) (Φ.inv_mem hf)
    have hu2 : (t * (f * t * f⁻¹)) * (t * (f * t * f⁻¹)) = 1 := by
      have hs2 : (f * t * f⁻¹) * (f * t * f⁻¹) = 1 := by
        calc (f * t * f⁻¹) * (f * t * f⁻¹) = f * (t * t) * f⁻¹ := by group
          _ = 1 := by rw [hsq]; group
      calc (t * (f * t * f⁻¹)) * (t * (f * t * f⁻¹))
          = t * ((f * t * f⁻¹) * t) * (f * t * f⁻¹) := by group
        _ = t * (t * (f * t * f⁻¹)) * (f * t * f⁻¹) := by rw [hts]
        _ = (t * t) * ((f * t * f⁻¹) * (f * t * f⁻¹)) := by group
        _ = 1 := by rw [hsq, hs2, one_mul]
    have hu1 : t * (f * t * f⁻¹) = 1 := eq_one_of_sq_of_odd hΦodd huΦ hu2
    apply hneq
    rw [eq_inv_of_mul_eq_one_right hu1, htinv]
  have hF : ⁅Φ, Subgroup.zpowers t⁆ ≤ H₁ ⊓ Φ := by
    rw [Subgroup.commutator_le]
    intro f hf a ha
    rcases eq_one_or_eq_of_mem_zpowers hsq ha with h | h
    · rw [h, commutatorElement_one_right]
      exact (H₁ ⊓ Φ).one_mem
    · rw [h, commutatorElement_def]
      refine ⟨H₁.mul_mem (hconjH₁ f hf) (H₁.inv_mem htH₁), ?_⟩
      have e : f * t * f⁻¹ * t⁻¹ = f * (t * f⁻¹ * t⁻¹) := by group
      rw [e]
      exact Φ.mul_mem hf (htΦ _ (Φ.inv_mem hf))
  have hcardH₁ : Nat.card H₁ = 6 := hb.card_eq H₁ hH₁
  have hdvd6 : Nat.card ↥(H₁ ⊓ Φ) ∣ 6 := hcardH₁ ▸ Subgroup.card_dvd_of_le inf_le_left
  have hoddI : Odd (Nat.card ↥(H₁ ⊓ Φ)) :=
    Odd.of_dvd_nat hΦodd (Subgroup.card_dvd_of_le inf_le_right)
  have hI13 : Nat.card ↥(H₁ ⊓ Φ) = 1 ∨ Nat.card ↥(H₁ ⊓ Φ) = 3 := by
    obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥(H₁ ⊓ Φ) = n := ⟨_, rfl⟩
    rw [hn] at hdvd6 hoddI ⊢
    have hn6 : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    rw [Nat.odd_iff] at hoddI
    interval_cases n <;> omega
  obtain ⟨f₀, hf₀, hf₀t⟩ := hnt
  set x := ⁅f₀, t⁆ with hxdef
  have hxF : x ∈ ⁅Φ, Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mem_commutator hf₀ (Subgroup.mem_zpowers t)
  have hx1 : x ≠ 1 := by
    intro h
    rw [hxdef, commutatorElement_eq_one_iff_mul_comm] at h
    exact hf₀t h
  have hxI : x ∈ H₁ ⊓ Φ := hF hxF
  have hxΦ : x ∈ Φ := hxI.2
  have hI3 : Nat.card ↥(H₁ ⊓ Φ) = 3 := by
    rcases hI13 with h | h
    · exfalso
      have := Subgroup.eq_bot_of_card_eq _ h
      rw [this, Subgroup.mem_bot] at hxI
      exact hx1 hxI
    · exact h
  have hzx : Subgroup.zpowers x = H₁ ⊓ Φ := by
    have hle : Subgroup.zpowers x ≤ H₁ ⊓ Φ := Subgroup.zpowers_le.2 hxI
    have hd : Nat.card (Subgroup.zpowers x) ∣ 3 := hI3 ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exfalso
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
      exact hx1 h
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hI3, h])
  have hFeq : ⁅Φ, Subgroup.zpowers t⁆ = Subgroup.zpowers x :=
    le_antisymm (hzx ▸ hF) (Subgroup.zpowers_le.2 hxF)
  have htx : t * x * t⁻¹ = x⁻¹ := by
    have e1 : t * x * t⁻¹ = t * f₀ * t * f₀⁻¹ := by
      rw [hxdef, commutatorElement_def, htinv]
      calc t * (f₀ * t * f₀⁻¹ * t) * t = t * f₀ * t * f₀⁻¹ * (t * t) := by group
        _ = t * f₀ * t * f₀⁻¹ := by rw [hsq, mul_one]
    have e2 : x⁻¹ = t * f₀ * t * f₀⁻¹ := by
      calc x⁻¹ = t * f₀ * t⁻¹ * f₀⁻¹ := by rw [hxdef, commutatorElement_def]; group
        _ = t * f₀ * t * f₀⁻¹ := by rw [htinv]
    rw [e1, e2]
  have hxn : x ^ Nat.card Φ = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' : (⟨x, hxΦ⟩ : ↥Φ) ^ Nat.card Φ = 1)
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  obtain ⟨hwM, hfix, hcard4, hx3⟩ :=
    B1.inverted_by_transvection hV htw ht1 hΦodd hxn hx1 htx
  have hcentral : ∀ g ∈ Φ, g * x = x * g := by
    intro g hg
    have hgx : g * x * g⁻¹ ∈ Subgroup.zpowers x := by
      rw [hzx]
      refine ⟨?_, Φ.mul_mem (Φ.mul_mem hg hxΦ) (Φ.inv_mem hg)⟩
      have e : g * x * g⁻¹ = ((g * f₀) * t * (g * f₀)⁻¹) * (g * t * g⁻¹)⁻¹ := by
        rw [hxdef, commutatorElement_def]
        group
      rw [e]
      exact H₁.mul_mem (hconjH₁ _ (Φ.mul_mem hg hf₀)) (H₁.inv_mem (hconjH₁ g hg))
    rcases eq_of_mem_zpowers_three hx3 hgx with h | h | h
    · exfalso
      apply hx1
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    · calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
    · exfalso
      have hg2 : Commute (g ^ 2) x := by
        have e : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
          calc g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by rw [pow_two]; group
            _ = g * x⁻¹ * g⁻¹ := by rw [h]
            _ = (g * x * g⁻¹)⁻¹ := by group
            _ = x := by rw [h, inv_inv]
        calc g ^ 2 * x = g ^ 2 * x * (g ^ 2)⁻¹ * g ^ 2 := by group
          _ = x * g ^ 2 := by rw [e]
      have hgn : g ^ Nat.card Φ = 1 := by
        have h' := congrArg Subtype.val (pow_card_eq_one' : (⟨g, hg⟩ : ↥Φ) ^ Nat.card Φ = 1)
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
      have hgeq : (g ^ 2) ^ ((Nat.card Φ + 1) / 2) = g := by
        rw [← pow_mul, mul_comm, pow_mul]
        exact sq_pow_half hΦodd hgn
      have hgc : Commute g x := hgeq ▸ hg2.pow_left _
      have h1 : g * x * g⁻¹ = x := by rw [hgc.eq, mul_inv_cancel_right]
      rw [h1] at h
      have hxx : x * x = 1 := by
        calc x * x = x * x⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel x
      apply hx1
      calc x = x ^ 3 * (x * x)⁻¹ := by rw [pow_succ, pow_two]; group
        _ = 1 := by rw [hx3, hxx]; group
  have hinverted : ∀ y ∈ Φ, t * y * t⁻¹ = y⁻¹ → y ∈ Subgroup.zpowers x := by
    intro y hy hty
    set z := y ^ ((Nat.card Φ + 1) / 2) with hz
    have hzΦ : z ∈ Φ := Φ.pow_mem hy _
    have htz : t * z * t⁻¹ = z⁻¹ := by
      rw [hz, ← conj_pow, hty, inv_pow]
    have hcomm : ⁅z, t⁆ = z ^ 2 := by
      rw [commutatorElement_def]
      calc z * t * z⁻¹ * t⁻¹ = z * (t * z * t⁻¹)⁻¹ := by group
        _ = z * z := by rw [htz, inv_inv]
        _ = z ^ 2 := (pow_two z).symm
    have hyn : y ^ Nat.card Φ = 1 := by
      have h' := congrArg Subtype.val (pow_card_eq_one' : (⟨y, hy⟩ : ↥Φ) ^ Nat.card Φ = 1)
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
    have hy' : y = ⁅z, t⁆ := by rw [hcomm, hz]; exact (sq_pow_half hΦodd hyn).symm
    rw [hy', ← hFeq]
    exact Subgroup.commutator_mem_commutator hzΦ (Subgroup.mem_zpowers t)
  have hGle : Subgroup.zpowers x ⊔ Subgroup.zpowers t ≤ H₁ :=
    sup_le (Subgroup.zpowers_le.2 hxI.1) (Subgroup.zpowers_le.2 htH₁)
  have hcardt : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) ht1
  have hGeq : Subgroup.zpowers x ⊔ Subgroup.zpowers t = H₁ := by
    have h3 : 3 ∣ Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) :=
      (card_zpowers_eq_three hx3 hx1) ▸ Subgroup.card_dvd_of_le le_sup_left
    have h2 : 2 ∣ Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) :=
      hcardt ▸ Subgroup.card_dvd_of_le le_sup_right
    have h6 : 6 ∣ Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) := Nat.card_pos
    exact Subgroup.eq_of_le_of_card_ge hGle (by rw [hcardH₁]; exact Nat.le_of_dvd hpos h6)
  have hMeq : commSub (⊤ : Subgroup V) (Subgroup.zpowers x) = commSub ⊤ H₁ :=
    Subgroup.eq_of_le_of_card_ge (commSub_mono le_rfl (Subgroup.zpowers_le.2 hxI.1))
      (by rw [hb.card_comm H₁ hH₁, hcard4])
  have hnat := actsAsNaturalL2_of_full hV (hb.card_comm H₁ hH₁) (hb.le_stabSub hH₁)
    (hb.inf_centSub hH₁) (hb.autSub_eq_top H₁ hH₁)
  obtain ⟨e, -, -⟩ := hnat
  refine ⟨x, ⟨htw, ht1, hxΦ, hx1, hx3, htx, hFeq, ?_, ?_, hfix, hcentral, hinverted, ?_, ?_, ?_,
    ?_⟩⟩
  · rw [commV_eq_commSub]
    exact hcard4
  · rw [commV_eq_commSub]
    exact hwM
  · rw [hGeq]
    exact hcardH₁
  · rw [hGeq, commV_eq_commSub, hMeq]
    exact hb.inf_centSub hH₁
  · rw [hGeq, commV_eq_commSub, hMeq]
    exact hb.autSub_eq_top H₁ hH₁
  · rw [hGeq]
    exact ⟨e⟩

end CFSG.Quasithin.B19
