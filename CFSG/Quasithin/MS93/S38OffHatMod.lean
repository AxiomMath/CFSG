module

public import CFSG.Quasithin.Background.SmithB42HatA6Off
public import CFSG.Quasithin.Background.SmithB42Alt6Fix
public import CFSG.Quasithin.EmptyFaithful.LRed6Hat

public section

namespace CFSG.Quasithin.MS93.S38H

open CFSG.Quasithin CFSG.Open

variable {V : Type} [CommGroup V]

structure HatMod (H : Subgroup (MulAut V)) : Prop where
  sq : ∀ v : V, v ^ 2 = 1
  card : Nat.card V = 2 ^ 6
  perf : Group.IsPerfect ↥H
  center : Nat.card (Subgroup.center ↥H) = 3
  quot : Nonempty (↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6))

theorem HatMod.of_tripleA6Six (hsq : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    (h6 : TripleA6Six H ⊤ ⊥) : HatMod H := by
  have hcard := (LRed6.hat_conclusion h6).2
  obtain ⟨K, hK, hKf, Γ₀, -, -, hhat, -, π, hπ⟩ := h6
  have hinj : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hH : IsHat ↥H ↥(alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) hhat
  exact ⟨hsq, hcard, hH.1.1, hH.2.1, hH.2.2⟩

namespace HatMod

variable {H : Subgroup (MulAut V)} (hH : HatMod H)
include hH

theorem finite : Finite V :=
  Nat.finite_of_card_ne_zero (by rw [hH.card]; norm_num)

theorem card_H : Nat.card H = 1080 :=
  (HatA6.quasisimple_card hH.perf hH.center hH.quot.some).2

theorem irr : ∀ W : Subgroup V, (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤ :=
  have := hH.finite
  (H13.hatA6SixIrreducible V hH.sq hH.card H hH.perf hH.center hH.quot).2

theorem exists_z : ∃ zH : ↥H, Subgroup.center ↥H = Subgroup.zpowers zH ∧
    (zH : MulAut V) ^ 3 = 1 ∧ ∀ v : V, (zH : MulAut V) v = v → v = 1 :=
  have := hH.finite
  HatA6.exists_center_fpf hH.sq hH.card hH.perf hH.center hH.quot.some

theorem mem_of_comm {x : MulAut V} (hxN : x ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hxz : ∀ k ∈ Subgroup.center ↥H, x * (k : MulAut V) = (k : MulAut V) * x) : x ∈ H :=
  have := hH.finite
  HatA6.mem_of_normalizes hH.sq hH.card hH.perf hH.center hH.quot.some hH.irr
    (Subgroup.mem_normalizer_iff.mp hxN) hxz

theorem card_ne_eight {S : Subgroup (MulAut V)} (hSH : S ≤ H)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : Nat.card S ≠ 8 := by
  intro h8
  obtain ⟨e⟩ := hH.quot
  set φ : ↥H →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥H)) with hφ
  set S' : Subgroup ↥H := S.subgroupOf H with hS'
  have hS'c : Nat.card S' = 8 := by
    rw [← h8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have hinj : Function.Injective (φ.comp S'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : (x : ↥H) ∈ Subgroup.center ↥H := by
      have h1 : QuotientGroup.mk' (Subgroup.center ↥H) (x : ↥H) = 1 := by
        apply e.injective
        simpa [hφ] using hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h3 : orderOf (⟨(x : ↥H), hxc⟩ : ↥(Subgroup.center ↥H)) ∣ 3 :=
      hH.center ▸ orderOf_dvd_natCard _
    have h8' : orderOf x ∣ 8 := hS'c ▸ orderOf_dvd_natCard x
    have h3'' : orderOf (x : ↥H) ∣ 3 :=
      (Subgroup.orderOf_coe (⟨(x : ↥H), hxc⟩ : ↥(Subgroup.center ↥H))) ▸ h3
    have h3' : orderOf x ∣ 3 := (Subgroup.orderOf_coe x) ▸ h3''
    have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h3' h8'
    exact orderOf_eq_one_iff.mp h1
  set D : Subgroup (alternatingGroup (Fin 6)) := (φ.comp S'.subtype).range with hD
  have hDc : Nat.card D = 8 := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hS'c]
  obtain ⟨⟨_, ⟨a, rfl⟩⟩, ⟨_, ⟨b, rfl⟩⟩, hab⟩ := B42Alt6.not_comm_of_card_eight D hDc
  have hab' : a * b = b * a := Subtype.ext (Subtype.ext
    (hS _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)))
  apply hab
  apply Subtype.ext
  show (φ.comp S'.subtype) a * (φ.comp S'.subtype) b =
    (φ.comp S'.subtype) b * (φ.comp S'.subtype) a
  rw [← map_mul, ← map_mul, hab']

theorem card_le_eight {P : Subgroup (MulAut V)} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    Nat.card P ≤ 8 := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH.card_H]; norm_num)
  have : Finite P := Finite.of_injective _ (Subgroup.inclusion_injective hPH)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hd : 2 ^ k ∣ 1080 := hk ▸ hH.card_H ▸ Subgroup.card_dvd_of_le hPH
  rw [hk]
  by_contra hlt
  have hk4 : 4 ≤ k := by
    by_contra hk4
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h16 : 2 ^ 4 ∣ 1080 := (Nat.pow_dvd_pow 2 hk4).trans hd
  omega

theorem card_le_four {P : Subgroup (MulAut V)} (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : Nat.card P ≤ 4 := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH.card_H]; norm_num)
  have : Finite P := Finite.of_injective _ (Subgroup.inclusion_injective hPH)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have h8 := hH.card_le_eight hPH hP
  have h8' := hH.card_ne_eight hPH hc
  rw [hk] at h8 h8' ⊢
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp_all

omit hH in
theorem isPGroup_of_isElemAbelian2 {E : Subgroup (MulAut V)} (hE : IsElemAbelian2 E) :
    IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩

theorem mem_of_comm_z {zH : ↥H} (hcen : Subgroup.center ↥H = Subgroup.zpowers zH)
    {x : MulAut V} (hxN : x ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hxz : x * zH = zH * x) : x ∈ H := by
  refine hH.mem_of_comm hxN fun k hk => ?_
  rw [hcen] at hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  rw [Subgroup.coe_zpow]
  exact (Commute.zpow_right hxz n).eq

omit hH in
theorem comm_z_of_mem {zH : ↥H} (hcen : Subgroup.center ↥H = Subgroup.zpowers zH) {x : MulAut V}
    (hx : x ∈ H) : x * zH = zH * x := by
  have hzc : zH ∈ Subgroup.center ↥H := hcen ▸ Subgroup.mem_zpowers zH
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨x, hx⟩)

omit hH in
theorem z_mem_fixV {z : MulAut V} {E : Subgroup (MulAut V)} (hEz : ∀ b ∈ E, b * z = z * b)
    {v : V} (hv : v ∈ fixV E) : z v ∈ fixV E := by
  intro b hb
  have := congrArg (fun y : MulAut V => y v) (hEz b hb)
  change b (z v) = z (b v) at this
  rw [this, hv b hb]

theorem card_fixV_le {zH : ↥H} (h3 : (zH : MulAut V) ^ 3 = 1)
    (hfp : ∀ v : V, (zH : MulAut V) v = v → v = 1) {E : Subgroup (MulAut V)}
    (hEz : ∀ b ∈ E, b * zH = zH * b) (hE1 : E ≠ ⊥) : Nat.card (fixV E) ≤ 16 := by
  have := hH.finite
  rcases HatA6.card_cases_of_inv hH.card h3 hfp (fun s hs => z_mem_fixV hEz hs) with
    h | h | h | h
  · omega
  · omega
  · omega
  · exfalso
    apply hE1
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    have htop : fixV E = ⊤ := Subgroup.eq_top_of_card_eq _ (h.trans hH.card.symm)
    exact MulEquiv.ext fun v => (htop ▸ Subgroup.mem_top v : v ∈ fixV E) b hb

theorem comm_z {zH : ↥H} (hcen : Subgroup.center ↥H = Subgroup.zpowers zH)
    (h3 : (zH : MulAut V) ^ 3 = 1) (hfp : ∀ v : V, (zH : MulAut V) v = v → v = 1)
    {E : Subgroup (MulAut V)} (hEN : E ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hE : IsElemAbelian2 E) (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) :
    ∀ b ∈ E, b * zH = zH * b := by
  classical
  have := hH.finite
  set z : MulAut V := (zH : MulAut V) with hzdef
  have hz1 : z ≠ 1 := by
    intro h1
    have htop : (⊤ : Subgroup V) = ⊥ := by
      rw [eq_bot_iff]
      intro v _
      exact hfp v (by rw [h1, MulAut.one_apply])
    have := hH.card
    rw [← Subgroup.card_top (G := V), htop, Subgroup.card_bot] at this
    norm_num at this
  by_contra hcon
  push Not at hcon
  obtain ⟨t, htE, htz⟩ := hcon
  have ht2 : t * z = z * z * t :=
    (HatA6.conj_z_cases hcen h3 hz1 (hEN htE)).resolve_left htz
  have htz' : ∀ v, t (z v) = z (z (t v)) := fun v => congrArg (fun y : MulAut V => y v) ht2
  set E₀ := E ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) with hE₀
  have hE₀E : E₀ ≤ E := inf_le_left
  have hE₀z : ∀ b ∈ E₀, b * z = z * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.1 hb.2
  have hE₀H : E₀ ≤ H := fun b hb => hH.mem_of_comm_z hcen (hEN (hE₀E hb)) (hE₀z b hb)
  have hE₀e : IsElemAbelian2 E₀ :=
    ⟨fun a ha b hb => hE.1 a (hE₀E ha) b (hE₀E hb), fun a ha => hE.2 a (hE₀E ha)⟩
  have hE₀4 : Nat.card E₀ ≤ 4 :=
    hH.card_le_four hE₀H (isPGroup_of_isElemAbelian2 hE₀e) hE₀e.1
  have hbt : ∀ b ∈ E, b ∉ E₀ → b * t ∈ E₀ := by
    intro b hb hb0
    have hbz : b * z = z * z * b := by
      rcases HatA6.conj_z_cases hcen h3 hz1 (hEN hb) with h | h
      · exact absurd ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 h⟩ hb0
      · exact h
    refine ⟨E.mul_mem hb htE, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hz3 : z * z * z = 1 := by rw [← pow_three']; exact h3
    calc b * t * z = b * (t * z) := by group
      _ = b * (z * z * t) := by rw [ht2]
      _ = (b * z) * z * t := by group
      _ = (z * z * b) * z * t := by rw [hbz]
      _ = z * z * (b * z) * t := by group
      _ = z * z * (z * z * b) * t := by rw [hbz]
      _ = z * (z * z * z) * b * t := by group
      _ = z * (b * t) := by rw [hz3]; group
  have hcardE₀ : Nat.card E ≤ 2 * Nat.card E₀ := by
    let f : ↥E → ↥E₀ ⊕ ↥E₀ := fun b =>
      if hb : (b : MulAut V) ∈ E₀ then Sum.inl ⟨b, hb⟩
      else Sum.inr ⟨b * t, hbt b b.2 hb⟩
    have hf : Function.Injective f := by
      intro b b' h
      by_cases h1 : (b : MulAut V) ∈ E₀ <;> by_cases h2 : (b' : MulAut V) ∈ E₀
      · simp only [f, h1, h2, dite_true, Sum.inl.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext h
      · simp [f, h1, h2] at h
      · simp [f, h1, h2] at h
      · simp only [f, h1, h2, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext (mul_right_cancel h)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum, ← two_mul] at this
  have hfixE : fixV E = fixV E₀ ⊓ fixV (Subgroup.zpowers t) := by
    ext v
    constructor
    · intro hv
      exact ⟨fun b hb => hv b (hE₀E hb), (HatA6.mem_fixV_zpowers_iff).2 (hv t htE)⟩
    · rintro ⟨hv0, hvt⟩ b hb
      have hvt' : t v = v := (HatA6.mem_fixV_zpowers_iff).1 hvt
      by_cases hb0 : b ∈ E₀
      · exact hv0 b hb0
      · have ht22 : t * t = 1 := by rw [← pow_two]; exact hE.2 t htE
        have h1 := hv0 _ (hbt b hb hb0)
        calc b v = (b * t * t) v := by rw [mul_assoc, ht22, mul_one]
          _ = (b * t) (t v) := rfl
          _ = v := by rw [hvt', h1]
  have hdesc := HatA6.card_sq_le_of_semilinear hfp htz' (fun u hu => z_mem_fixV hE₀z hu)
  rw [← hfixE] at hdesc
  have hV : Nat.card V = 64 := by rw [hH.card]; norm_num
  rw [hV] at hoff
  by_cases hE₀1 : E₀ = ⊥
  · have hc1 : Nat.card E₀ = 1 := by rw [hE₀1, Subgroup.card_bot]
    have hfE₀ : Nat.card (fixV E₀) ≤ 64 := hV ▸ Subgroup.card_le_card_group _
    have h8 : Nat.card (fixV E) ≤ 8 := by nlinarith
    have : Nat.card E * Nat.card (fixV E) ≤ 2 * 8 := Nat.mul_le_mul (by omega) h8
    omega
  · have h16 := hH.card_fixV_le h3 hfp hE₀z hE₀1
    have h4 : Nat.card (fixV E) ≤ 4 := by nlinarith
    have : Nat.card E * Nat.card (fixV E) ≤ 8 * 4 := Nat.mul_le_mul (by omega) h4
    omega

theorem offender_basic {E : Subgroup (MulAut V)}
    (hEN : E ≤ Subgroup.normalizer (H : Set (MulAut V))) (hE : IsElemAbelian2 E) (hE1 : E ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) :
    E ≤ H ∧ Nat.card E = 4 ∧ Nat.card (fixV E) = 16 := by
  have := hH.finite
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have hEz := hH.comm_z hcen h3 hfp hEN hE hoff
  have hEH : E ≤ H := fun b hb => hH.mem_of_comm_z hcen (hEN hb) (hEz b hb)
  have hE4 := hH.card_le_four hEH (isPGroup_of_isElemAbelian2 hE) hE.1
  have h16 := hH.card_fixV_le h3 hfp hEz hE1
  have hV : Nat.card V = 64 := by rw [hH.card]; norm_num
  rw [hV] at hoff
  have := HatA6.card_cases_of_inv (hH.card) h3 hfp (fun s hs => z_mem_fixV hEz hs)
  refine ⟨hEH, ?_, ?_⟩
  · rcases this with h | h | h | h <;> rw [h] at hoff h16 <;> omega
  · rcases this with h | h | h | h <;> rw [h] at hoff h16 ⊢ <;> omega

omit hH in
theorem comm_mem_fixV_zpowers (hsq : ∀ v : V, v ^ 2 = 1) {e : MulAut V} (he : e ^ 2 = 1)
    (v : V) : e v * v⁻¹ ∈ fixV (Subgroup.zpowers e) := by
  have hinv : ∀ w : V, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq w)
  have hee : e (e v) = v := by
    rw [← MulAut.mul_apply, ← pow_two, he, MulAut.one_apply]
  rw [HatA6.mem_fixV_zpowers_iff, map_mul, map_inv, hee, hinv (e v), hinv v, mul_comm]

omit hH in
theorem mem_commV_of_normalizes {E : Subgroup (MulAut V)} {s : MulAut V}
    (hs : ∀ x ∈ E, s * x * s⁻¹ ∈ E) {m : V} (hm : m ∈ commV E) : s m ∈ commV E :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hs hm

theorem fixV_zpowers_eq {zH : ↥H} (h3 : (zH : MulAut V) ^ 3 = 1)
    (hfp : ∀ v : V, (zH : MulAut V) v = v → v = 1) {E : Subgroup (MulAut V)}
    (hEz : ∀ b ∈ E, b * zH = zH * b) (hf : Nat.card (fixV E) = 16) {e : MulAut V} (he : e ∈ E)
    (he1 : e ≠ 1) : fixV (Subgroup.zpowers e) = fixV E := by
  have := hH.finite
  have hle : fixV E ≤ fixV (Subgroup.zpowers e) := fun v hv =>
    (HatA6.mem_fixV_zpowers_iff).2 (hv e he)
  have hz : ∀ b ∈ Subgroup.zpowers e, b * zH = zH * b := by
    intro b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (hEz e he) n).eq
  have hne : Subgroup.zpowers e ≠ ⊥ := fun h =>
    he1 (by simpa using (h ▸ Subgroup.mem_zpowers e : e ∈ (⊥ : Subgroup (MulAut V))))
  have h16 := hH.card_fixV_le h3 hfp hz hne
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hf]; exact h16)).symm

theorem comm_mem_fixV {zH : ↥H} (h3 : (zH : MulAut V) ^ 3 = 1)
    (hfp : ∀ v : V, (zH : MulAut V) v = v → v = 1) {E : Subgroup (MulAut V)}
    (hE : IsElemAbelian2 E) (hEz : ∀ b ∈ E, b * zH = zH * b) (hf : Nat.card (fixV E) = 16)
    {e : MulAut V} (he : e ∈ E) (v : V) : e v * v⁻¹ ∈ fixV E := by
  by_cases he1 : e = 1
  · rw [he1, MulAut.one_apply, mul_inv_cancel]
    exact (fixV E).one_mem
  · rw [← hH.fixV_zpowers_eq h3 hfp hEz hf he he1]
    exact comm_mem_fixV_zpowers hH.sq (hE.2 e he) v

theorem commV_le_fixV {zH : ↥H} (h3 : (zH : MulAut V) ^ 3 = 1)
    (hfp : ∀ v : V, (zH : MulAut V) v = v → v = 1) {E : Subgroup (MulAut V)}
    (hE : IsElemAbelian2 E) (hEz : ∀ b ∈ E, b * zH = zH * b) (hf : Nat.card (fixV E) = 16) :
    commV E ≤ fixV E := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨x, hx, v, rfl⟩
  exact hH.comm_mem_fixV h3 hfp hE hEz hf hx v

theorem fixV_le_commV {E : Subgroup (MulAut V)} (hEH : E ≤ H) (hE : IsElemAbelian2 E)
    (hE4 : Nat.card E = 4) (hf : Nat.card (fixV E) = 16) : fixV E ≤ commV E := by
  have := hH.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  set z : MulAut V := (zH : MulAut V) with hzdef
  have hHz : ∀ x ∈ H, x * z = z * x := fun x hx => comm_z_of_mem hcen hx
  have hEz : ∀ b ∈ E, b * z = z * b := fun b hb => hHz b (hEH hb)
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE4
    norm_num at hE4
  by_contra hW
  set W := fixV E with hWdef
  set ℓ := commV E with hℓdef
  have hℓW : ℓ ≤ W := hH.commV_le_fixV h3 hfp hE hEz hf
  have hzℓ : ∀ m ∈ ℓ, z m ∈ ℓ := fun m hm =>
    mem_commV_of_normalizes (fun x hx => by rw [← hEz x hx, mul_inv_cancel_right]; exact hx) hm
  have hℓ1 : ℓ ≠ ⊥ := by
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE1
    have hx1' : (x : MulAut V) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v, (x : MulAut V) v ≠ v := by
      by_contra hcon
      push Not at hcon
      exact hx1' (MulEquiv.ext hcon)
    intro hbot
    have hm : (x : MulAut V) v * v⁻¹ ∈ ℓ := Subgroup.subset_closure ⟨x, x.2, v, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hv hm
  have hℓ4 : Nat.card ℓ = 4 := by
    have hle := Subgroup.card_le_of_le hℓW
    rw [hf] at hle
    rcases HatA6.card_cases_of_inv hH.card h3 hfp hzℓ with h | h | h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hℓ1
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hℓW (by rw [h, hf])).ge hW
    · omega
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH.card_H]; norm_num)
  have hE'c : Nat.card (E.subgroupOf H) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hE4]
    norm_num
  obtain ⟨K, hKc, hEK⟩ := Sylow.exists_subgroup_card_pow_succ (p := 2) (n := 2)
    (by rw [hH.card_H]; norm_num) hE'c
  set S : Subgroup (MulAut V) := K.map H.subtype with hSdef
  have hSH : S ≤ H := Subgroup.map_subtype_le K
  have hSc : Nat.card S = 8 := by
    rw [hSdef, Subgroup.card_map_of_injective H.subtype_injective, hKc]
    norm_num
  have hES : E ≤ S := fun x hx =>
    ⟨⟨x, hEH hx⟩, hEK (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hSz : ∀ s ∈ S, s * z = z * s := fun s hs => hHz s (hSH hs)
  have : Finite S := Finite.of_injective _ (Subgroup.inclusion_injective hSH)
  have hidx : (E.subgroupOf S).index = 2 := by
    have h1 := (E.subgroupOf S).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv, hE4, hSc] at h1
    omega
  have hEn : (E.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hidx
  have hSN : S ≤ Subgroup.normalizer (E : Set (MulAut V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).mp hEn
  have hSn : ∀ s ∈ S, ∀ x ∈ E, s * x * s⁻¹ ∈ E := fun s hs x hx =>
    (Subgroup.mem_normalizer_iff.mp (hSN hs) x).mp hx
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 3) (by rw [hSc]; norm_num)
  obtain ⟨m, hmℓ, hm1, hmS⟩ := B1.exists_fixed_ne_one hH.sq hSp
    (fun s hs m hm => mem_commV_of_normalizes (hSn s hs) hm) hℓ1
  have hℓS : ℓ ≤ fixV S := by
    set F := fixV S ⊓ ℓ with hF
    have hzF : ∀ v ∈ F, z v ∈ F := by
      rintro v ⟨hvS, hvℓ⟩
      refine ⟨fun s hs => ?_, hzℓ v hvℓ⟩
      have := congrArg (fun y : MulAut V => y v) (hSz s hs)
      change s (z v) = z (s v) at this
      rw [this, hvS s hs]
    have hmF : m ∈ F := ⟨fun s hs => hmS s hs, hmℓ⟩
    have hFℓ : F ≤ ℓ := inf_le_right
    have hle := Subgroup.card_le_of_le hFℓ
    rw [hℓ4] at hle
    have hF4 : Nat.card F = 4 := by
      rcases HatA6.card_cases_of_inv hH.card h3 hfp hzF with h | h | h | h
      · rw [Subgroup.card_eq_one] at h
        rw [h, Subgroup.mem_bot] at hmF
        exact absurd hmF hm1
      · exact h
      · omega
      · omega
    exact (Subgroup.eq_of_le_of_card_ge hFℓ (by rw [hℓ4, hF4])).ge.trans inf_le_left
  have : Group.IsNilpotent ↥S := hSp.isNilpotent
  have hEne : E.subgroupOf S ≠ ⊥ := by
    intro h
    apply hE1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hES hx⟩ : ↥S) ∈ E.subgroupOf S := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  obtain ⟨⟨y, hyE, hyc⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hEne)
  set e₁ : MulAut V := (y : MulAut V) with he₁
  have he₁E : e₁ ∈ E := Subgroup.mem_subgroupOf.mp hyE
  have he₁1 : e₁ ≠ 1 := by
    intro h
    apply hy1
    exact Subtype.ext (Subtype.ext h)
  have he₁S : ∀ s ∈ S, s * e₁ = e₁ * s := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨s, hs⟩)
  have hWe₁ := hH.fixV_zpowers_eq h3 hfp hEz hf he₁E he₁1
  have hSW : ∀ s ∈ S, ∀ v : V, s v * v⁻¹ ∈ W := by
    intro s hs v
    rw [hWdef, ← hWe₁, HatA6.mem_fixV_zpowers_iff]
    have hd : e₁ v * v⁻¹ ∈ ℓ := Subgroup.subset_closure ⟨e₁, he₁E, v, rfl⟩
    have hsd : s (e₁ v * v⁻¹) = e₁ v * v⁻¹ := hℓS hd s hs
    have hse : e₁ (s v) = s (e₁ v) := (congrArg (fun y : MulAut V => y v) (he₁S s hs)).symm
    set d := e₁ v * v⁻¹ with hd'
    have hev : e₁ v = d * v := by rw [hd']; simp
    rw [map_mul, map_inv, hse, hev, map_mul, hsd, ← div_eq_mul_inv, ← div_eq_mul_inv,
      mul_div_mul_left_eq_div, div_eq_mul_inv]
  have hScomm : ∀ s ∈ S, ∀ e ∈ E, e * s = s * e := by
    intro s hs e he
    refine MulEquiv.ext fun v => ?_
    show e (s v) = s (e v)
    have hw : s v * v⁻¹ ∈ W := hSW s hs v
    have hd : e v * v⁻¹ ∈ ℓ := Subgroup.subset_closure ⟨e, he, v, rfl⟩
    have hew : e (s v * v⁻¹) = s v * v⁻¹ := hw e he
    have hsd : s (e v * v⁻¹) = e v * v⁻¹ := hℓS hd s hs
    set w := s v * v⁻¹ with hw'
    set d := e v * v⁻¹ with hd'
    have hsv : s v = w * v := by rw [hw']; simp
    have hev : e v = d * v := by rw [hd']; simp
    rw [hsv, map_mul, hew, hev, map_mul, hsd, hsv, mul_left_comm]
  have hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    by_cases haE : a ∈ E
    · exact hScomm b hb a haE
    by_cases hbE : b ∈ E
    · exact (hScomm a ha b hbE).symm
    have hab : a * b ∈ E := by
      have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr
        (by simp only [Subgroup.mem_subgroupOf]; exact iff_of_false haE hbE)
      exact Subgroup.mem_subgroupOf.mp this
    have h := hScomm a ha (a * b) hab
    have : a * (b * a) = a * (a * b) := by rw [← mul_assoc]; exact h
    exact (mul_left_cancel this).symm
  exact hH.card_ne_eight hSH hSab hSc

theorem offender {E : Subgroup (MulAut V)}
    (hEN : E ≤ Subgroup.normalizer (H : Set (MulAut V))) (hE : IsElemAbelian2 E) (hE1 : E ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) :
    E ≤ H ∧ Nat.card E = 4 ∧ Nat.card (fixV E) = 16 ∧ fixV E ≤ commV E := by
  obtain ⟨hEH, hE4, hf⟩ := hH.offender_basic hEN hE hE1 hoff
  exact ⟨hEH, hE4, hf, hH.fixV_le_commV hEH hE hE4 hf⟩

theorem offender_unique {P E₁ E₂ : Subgroup (MulAut V)} (hP : IsPGroup 2 P) (h₁P : E₁ ≤ P)
    (h₂P : E₂ ≤ P) (h₁H : E₁ ≤ H) (h₂H : E₂ ≤ H) (he₁ : IsElemAbelian2 E₁)
    (he₂ : IsElemAbelian2 E₂) (hc₁ : Nat.card E₁ = 4) (hc₂ : Nat.card E₂ = 4)
    (hf₁ : Nat.card (fixV E₁) = 16) (hf₂ : Nat.card (fixV E₂) = 16) : E₁ = E₂ := by
  have := hH.finite
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have h₁z : ∀ b ∈ E₁, b * zH = zH * b := fun b hb => comm_z_of_mem hcen (h₁H hb)
  have h₂z : ∀ b ∈ E₂, b * zH = zH * b := fun b hb => comm_z_of_mem hcen (h₂H hb)
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH.card_H]; norm_num)
  by_contra hne
  set Q := E₁ ⊔ E₂ with hQ
  have hQH : Q ≤ H := sup_le h₁H h₂H
  have : Finite Q := Finite.of_injective _ (Subgroup.inclusion_injective hQH)
  have hQp : IsPGroup 2 Q := hP.to_le (sup_le h₁P h₂P)
  have hQ8 := hH.card_le_eight hQH hQp
  have hrel : E₁.relIndex Q * Nat.card E₁ = Nat.card Q := by
    have := Subgroup.relIndex_mul_card E₁ Q
    rwa [inf_eq_left.mpr le_sup_left] at this
  have hrel1 : E₁.relIndex Q ≠ 1 := by
    intro h1
    have hle : E₂ ≤ E₁ := le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1)
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hc₁, hc₂])).symm
  have hrel0 : E₁.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel2 : E₁.relIndex Q = 2 := by
    rw [hc₁] at hrel
    omega
  have hle2 : E₁.relIndex E₂ ≤ 2 :=
    hrel2 ▸ Subgroup.relIndex_le_of_le_right le_sup_right hrel0
  have hint : E₁ ⊓ E₂ ≠ ⊥ := by
    intro hbot
    have := Subgroup.relIndex_mul_card E₁ E₂
    rw [hbot, Subgroup.card_bot, hc₂] at this
    omega
  obtain ⟨⟨t, ht₁, ht₂⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hint
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hW : fixV E₁ = fixV E₂ := by
    rw [← hH.fixV_zpowers_eq h3 hfp h₁z hf₁ ht₁ ht1', hH.fixV_zpowers_eq h3 hfp h₂z hf₂ ht₂ ht1']
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := by
    intro a ha b hb
    refine MulEquiv.ext fun v => ?_
    show a (b v) = b (a v)
    have hwa : a v * v⁻¹ ∈ fixV E₂ := hW ▸ hH.comm_mem_fixV h3 hfp he₁ h₁z hf₁ ha v
    have hwb : b v * v⁻¹ ∈ fixV E₁ := hW.symm ▸ hH.comm_mem_fixV h3 hfp he₂ h₂z hf₂ hb v
    have h1 : b (a v * v⁻¹) = a v * v⁻¹ := hwa b hb
    have h2 : a (b v * v⁻¹) = b v * v⁻¹ := hwb a ha
    set wa := a v * v⁻¹ with hwa'
    set wb := b v * v⁻¹ with hwb'
    have hav : a v = wa * v := by rw [hwa']; simp
    have hbv : b v = wb * v := by rw [hwb']; simp
    rw [hbv, map_mul, h2, hav, map_mul, h1, hbv, mul_left_comm]
  have hC₁ : Q ≤ Subgroup.centralizer (E₁ : Set (MulAut V)) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => he₁.1 x hx a ha
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx b hb
  have hC₂ : Q ≤ Subgroup.centralizer (E₂ : Set (MulAut V)) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcomm a ha x hx).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => he₂.1 x hx b hb
  have hQC : Q ≤ Subgroup.centralizer (Q : Set (MulAut V)) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp hC₁) (Subgroup.le_centralizer_iff.mp hC₂)
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hQC hb) a ha
  rw [hc₁] at hrel
  exact hH.card_ne_eight hQH hQab (by omega)

theorem mem_of_comm_of_mem {P E : Subgroup (MulAut V)} (hP : IsPGroup 2 P) (hEP : E ≤ P)
    (hEH : E ≤ H) (hE : IsElemAbelian2 E) (hE4 : Nat.card E = 4) {y : MulAut V} (hyP : y ∈ P)
    (hyH : y ∈ H) (hyE : ∀ e ∈ E, e * y = y * e) : y ∈ E := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH.card_H]; norm_num)
  set Q := E ⊔ Subgroup.zpowers y with hQ
  have hQH : Q ≤ H := sup_le hEH ((Subgroup.zpowers_le).mpr hyH)
  have : Finite Q := Finite.of_injective _ (Subgroup.inclusion_injective hQH)
  have hQp : IsPGroup 2 Q := hP.to_le (sup_le hEP ((Subgroup.zpowers_le).mpr hyP))
  have hyc : ∀ a ∈ Subgroup.zpowers y, ∀ e ∈ E, e * a = a * e := by
    intro a ha e he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_right (hyE e he) n).eq
  have hC₁ : Q ≤ Subgroup.centralizer (E : Set (MulAut V)) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => hE.1 x hx a ha
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => hyc b hb x hx
  have hC₂ : Q ≤ Subgroup.centralizer (Subgroup.zpowers y : Set (MulAut V)) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hyc x hx a ha).symm
    · refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self y m n).eq
  have hQC : Q ≤ Subgroup.centralizer (Q : Set (MulAut V)) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp hC₁) (Subgroup.le_centralizer_iff.mp hC₂)
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hQC hb) a ha
  have h4 := hH.card_le_four hQH hQp hQab
  have hEQ : E = Q :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hE4]; exact h4)
  rw [hEQ]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem comm_z_of_comm_mem {zH : ↥H} (hcen : Subgroup.center ↥H = Subgroup.zpowers zH)
    (h3 : (zH : MulAut V) ^ 3 = 1) (hfp : ∀ v : V, (zH : MulAut V) v = v → v = 1)
    {E : Subgroup (MulAut V)} (hEz : ∀ b ∈ E, b * zH = zH * b) (hf : Nat.card (fixV E) = 16)
    {y : MulAut V} (hyN : y ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hy : ∀ v : V, y v * v⁻¹ ∈ fixV E) : y * zH = zH * y := by
  have := hH.finite
  set z : MulAut V := (zH : MulAut V) with hzdef
  have hz1 : z ≠ 1 := by
    intro h1
    have htop : (⊤ : Subgroup V) = ⊥ := by
      rw [eq_bot_iff]
      intro v _
      exact hfp v (by rw [h1, MulAut.one_apply])
    have := hH.card
    rw [← Subgroup.card_top (G := V), htop, Subgroup.card_bot] at this
    norm_num at this
  rcases HatA6.conj_z_cases hcen h3 hz1 hyN with h | h
  · exact h
  · exfalso
    have hzz : ∀ w : V, z (z w) = w * z w := fun w =>
      H13.zz_eq_of_fpf hH.sq h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
    have hall : ∀ v : V, v ∈ fixV E := by
      intro v
      have h1 := hy v
      have h2 := hy (z v)
      have hyz : y (z v) = z (z (y v)) := congrArg (fun x : MulAut V => x v) h
      set w₁ := y v * v⁻¹ with hw₁
      have hyv : y v = w₁ * v := by rw [hw₁]; simp
      have hzw : z (z w₁) ∈ fixV E := z_mem_fixV hEz (z_mem_fixV hEz h1)
      have key : y (z v) * (z v)⁻¹ * (z (z w₁))⁻¹ = v := by
        rw [hyz, hyv, map_mul, map_mul, hzz v]
        simp [mul_comm, mul_assoc]
      rw [← key]
      exact (fixV E).mul_mem h2 ((fixV E).inv_mem hzw)
    have htop : fixV E = ⊤ := eq_top_iff.mpr fun v _ => hall v
    rw [htop, Subgroup.card_top, hH.card] at hf
    norm_num at hf

end HatMod

end CFSG.Quasithin.MS93.S38H
