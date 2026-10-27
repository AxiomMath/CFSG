module

public import CFSG.Quasithin.MS93.S38OffHatMod
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even6

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

section HatModule

variable {V : Type} [CommGroup V]

theorem zz_ch615 (hsq : ∀ v : V, v ^ 2 = 1) {z : MulAut V} (h3 : z ^ 3 = 1)
    (hfp : ∀ v, z v = v → v = 1) (v : V) : z (z v) = v * z v := by
  have hinv : ∀ x : V, x⁻¹ = x := fun x =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq x)
  have hz3 : z (z (z v)) = v := by
    have := congrArg (fun φ : MulAut V => φ v) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hn : v * z v * z (z v) = 1 := by
    apply hfp
    rw [map_mul, map_mul, hz3]
    ac_rfl
  calc z (z v) = (v * z v)⁻¹ := by rw [← mul_eq_one_iff_eq_inv]; rw [mul_comm]; exact hn
    _ = v * z v := hinv _

theorem sq_step_ch615 {z t : MulAut V} (h3 : z ^ 3 = 1) {P : Subgroup V}
    (hzP : ∀ w ∈ P, z w ∈ P) (htz : t * z = z * t) (htP : ∀ w ∈ P, t w = w) {u : V} :
    (t u * (z u)⁻¹ ∈ P → (t * t) u * (z (z u))⁻¹ ∈ P) ∧
      (t u * (z (z u))⁻¹ ∈ P → (t * t) u * (z u)⁻¹ ∈ P) := by
  have htz' : ∀ x, t (z x) = z (t x) := fun x => congrArg (fun φ : MulAut V => φ x) htz
  have hz3 : ∀ x, z (z (z x)) = x := fun x => by
    have := congrArg (fun φ : MulAut V => φ x) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  constructor
  · intro h
    set p := t u * (z u)⁻¹ with hp
    have htu : t u = p * z u := by rw [hp]; group
    have : (t * t) u * (z (z u))⁻¹ = p * z p := by
      rw [MulAut.mul_apply, htu, map_mul, htP p h, htz', htu, map_mul]
      group
    rw [this]
    exact P.mul_mem h (hzP p h)
  · intro h
    set p := t u * (z (z u))⁻¹ with hp
    have htu : t u = p * z (z u) := by rw [hp]; group
    have : (t * t) u * (z u)⁻¹ = p * z (z p) := by
      rw [MulAut.mul_apply, htu, map_mul, htP p h, htz', htz', htu, map_mul, map_mul, hz3]
      group
    rw [this]
    exact P.mul_mem h (hzP _ (hzP p h))

theorem comm_mem_of_fix_sixteen_ch615 [Finite V] (hsq : ∀ v : V, v ^ 2 = 1)
    (hV : Nat.card V = 2 ^ 6) {z : MulAut V} (h3 : z ^ 3 = 1) (hfp : ∀ v, z v = v → v = 1)
    {P : Subgroup V} (hzP : ∀ w ∈ P, z w ∈ P) (hP : Nat.card P = 16)
    {s : MulAut V} (hsz : s * z = z * s) {k : ℕ} (hs2 : s ^ 2 ^ k = 1)
    (hsP : ∀ w ∈ P, s w = w) (u : V) : s u * u⁻¹ ∈ P := by
  classical
  have hinv : ∀ x : V, x⁻¹ = x := fun x =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq x)
  have hzz := zz_ch615 hsq h3 hfp
  have hz3 : ∀ x, z (z (z x)) = x := fun x => by
    have := congrArg (fun φ : MulAut V => φ x) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  by_cases hu : u ∈ P
  · rw [hsP u hu, mul_inv_cancel]
    exact P.one_mem
  set M := P ⊔ Subgroup.closure ({u, z u} : Set V) with hM
  have hzM : ∀ w ∈ M, z w ∈ M := by
    have hle : M ≤ M.comap z.toMonoidHom := by
      refine sup_le (fun w hw => Subgroup.mem_sup_left (hzP w hw)) ?_
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · show z (z u) ∈ M
        rw [hzz]
        exact Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
    exact fun w hw => hle hw
  have huM : u ∈ M := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hMtop : M = ⊤ := by
    have hPM : P ≤ M := le_sup_left
    rcases HatA6.card_cases_of_inv hV h3 hfp hzM with h | h | h | h
    · have := Subgroup.card_le_of_le hPM
      omega
    · have := Subgroup.card_le_of_le hPM
      omega
    · exact absurd ((Subgroup.eq_of_le_of_card_ge hPM (by rw [h, hP])) ▸ huM) hu
    · exact Subgroup.eq_top_of_card_eq M (h.trans (by rw [hV]; norm_num))
  have hsuM : s u ∈ M := hMtop ▸ Subgroup.mem_top _
  obtain ⟨p, hp, m, hm, hpm⟩ := Subgroup.mem_sup.mp hsuM
  obtain ⟨a, b, hab⟩ := Subgroup.mem_closure_pair.mp hm
  have hpow : ∀ (x : V) (a : ℤ), x ^ a = 1 ∨ x ^ a = x := by
    intro x a
    rcases Int.even_or_odd a with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_ofNat, hsq, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_ofNat, hsq, one_zpow, one_mul, zpow_one]
  have hcls : s u * u⁻¹ ∈ P ∨ s u ∈ P ∨ s u * (z u)⁻¹ ∈ P ∨ s u * (z (z u))⁻¹ ∈ P := by
    rcases hpow u a with ha | ha <;> rcases hpow (z u) b with hb | hb <;>
      rw [ha, hb] at hab <;> subst hab
    · right; left
      rw [← hpm, mul_one, mul_one]
      exact hp
    · right; right; left
      rw [← hpm, one_mul, mul_inv_cancel_right]
      exact hp
    · left
      rw [← hpm, mul_one, mul_inv_cancel_right]
      exact hp
    · right; right; right
      rw [← hpm, ← hzz, mul_inv_cancel_right]
      exact hp
  have hiter : ∀ t : MulAut V, t * z = z * t → (∀ w ∈ P, t w = w) →
      (t u * (z u)⁻¹ ∈ P ∨ t u * (z (z u))⁻¹ ∈ P) →
      ∀ m : ℕ, (t ^ 2 ^ m) u * (z u)⁻¹ ∈ P ∨ (t ^ 2 ^ m) u * (z (z u))⁻¹ ∈ P := by
    intro t htz htP h0 m
    induction m with
    | zero => simpa using h0
    | succ m ih =>
      have htz' : t ^ 2 ^ m * z = z * t ^ 2 ^ m := (Commute.pow_left htz _).eq
      have htP' : ∀ w ∈ P, (t ^ 2 ^ m) w = w := fun w hw => by
        have key : ∀ j : ℕ, (t ^ j) w = w := by
          intro j
          induction j with
          | zero => rfl
          | succ j ihj => rw [pow_succ, MulAut.mul_apply, htP w hw, ihj]
        exact key _
      have hsq' : t ^ 2 ^ (m + 1) = t ^ 2 ^ m * t ^ 2 ^ m := by rw [pow_succ, pow_mul, sq]
      rw [hsq']
      obtain ⟨h1, h2⟩ := sq_step_ch615 h3 hzP htz' htP' (u := u)
      rcases ih with h | h
      · exact Or.inr (h1 h)
      · exact Or.inl (h2 h)
  rcases hcls with h | h | h | h
  · exact h
  · exfalso
    apply hu
    have := hsP _ h
    have hs1 : s⁻¹ (s u) = u := by simp
    rw [← hs1]
    have : s⁻¹ (s u) = s u := by
      calc s⁻¹ (s u) = s⁻¹ (s (s u)) := by rw [this]
        _ = s u := by simp
    rw [this]
    exact h
  all_goals exfalso
  all_goals
    have hfin := hiter s hsz hsP (by first | exact Or.inl h | exact Or.inr h) k
    rw [hs2, MulAut.one_apply] at hfin
    rcases hfin with h' | h'
    · apply hu
      have e : u * (z u)⁻¹ = z (z u) := by rw [hinv, hzz]
      rw [e] at h'
      have := hzP _ h'
      rwa [hz3] at this
    · apply hu
      have e : u * (z (z u))⁻¹ = z u := by
        rw [hinv, hzz, ← mul_assoc, ← pow_two, hsq, one_mul]
      rw [e] at h'
      have := hzP _ (hzP _ h')
      rwa [hz3] at this

theorem comm_of_card_fixV_sixteen_ch615 {H : Subgroup (MulAut V)} (hH : MS93.S38H.HatMod H)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : IsPGroup 2 S) (h16 : Nat.card (fixV S) = 16) :
    ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
  have := hH.finite
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have hSz : ∀ s ∈ S, s * zH = zH * s := fun s hs => MS93.S38H.HatMod.comm_z_of_mem hcen (hSH hs)
  have hzP : ∀ w ∈ fixV S, (zH : MulAut V) w ∈ fixV S := fun w hw =>
    MS93.S38H.HatMod.z_mem_fixV hSz hw
  have key : ∀ s ∈ S, ∀ v : V, s v * v⁻¹ ∈ fixV S := by
    intro s hs v
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact comm_mem_of_fix_sixteen_ch615 hH.sq hH.card h3 hfp hzP h16 (hSz s hs) hk'
      (fun w hw => hw s hs) v
  intro a ha b hb
  refine MulEquiv.ext fun v => ?_
  show a (b v) = b (a v)
  have hπb := key b hb v
  have hπa := key a ha v
  have e1 : b v = (b v * v⁻¹) * v := by group
  have e2 : a v = (a v * v⁻¹) * v := by group
  calc a (b v) = a ((b v * v⁻¹) * v) := by rw [← e1]
    _ = (b v * v⁻¹) * a v := by rw [map_mul, hπb a ha]
    _ = (b v * v⁻¹) * ((a v * v⁻¹) * v) := by rw [← e2]
    _ = (a v * v⁻¹) * ((b v * v⁻¹) * v) := by rw [mul_left_comm]
    _ = (a v * v⁻¹) * b v := by rw [← e1]
    _ = b ((a v * v⁻¹) * v) := by rw [map_mul, hπa b hb]
    _ = b (a v) := by rw [← e2]

theorem card_fixV_eq_four_ch615 {H : Subgroup (MulAut V)} (hH : MS93.S38H.HatMod H)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS8 : Nat.card S = 8) : Nat.card (fixV S) = 4 := by
  have := hH.finite
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have hSz : ∀ s ∈ S, s * zH = zH * s := fun s hs => MS93.S38H.HatMod.comm_z_of_mem hcen (hSH hs)
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 3) (by rw [hS8]; norm_num)
  have hS1 : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hS8
    norm_num at hS8
  have h16 := hH.card_fixV_le h3 hfp hSz hS1
  have htop : (⊤ : Subgroup V) ≠ ⊥ := by
    intro h
    have h1 := hH.card
    rw [← Subgroup.card_top (G := V), h, Subgroup.card_bot] at h1
    norm_num at h1
  obtain ⟨m, -, hm1, hmS⟩ := B1.exists_fixed_ne_one hH.sq hS (M := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _) htop
  have hne : fixV S ≠ ⊥ := fun h => hm1 (by
    have : m ∈ fixV S := fun s hs => hmS s hs
    rw [h, Subgroup.mem_bot] at this
    exact this)
  rcases HatA6.card_cases_of_inv hH.card h3 hfp
      (fun s hs => MS93.S38H.HatMod.z_mem_fixV hSz hs) with h | h | h | h
  · exact absurd (Subgroup.card_eq_one.mp h) hne
  · exact h
  · exact absurd hS8 (hH.card_ne_eight hSH (comm_of_card_fixV_sixteen_ch615 hH hSH hS h))
  · omega

theorem exists_stab_ch615 {H : Subgroup (MulAut V)} (hH : MS93.S38H.HatMod H)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS8 : Nat.card S = 8) :
    ∃ P : Subgroup (MulAut V), S ≤ P ∧ P ≤ H ∧ Nat.card P = 24 ∧
      (∀ p ∈ P, ∀ v ∈ fixV S, p v = v) ∧ (∀ p ∈ P, (∀ x ∈ H, p * x = x * p) → p = 1) := by
  classical
  have := hH.finite
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have h4 := card_fixV_eq_four_ch615 hH hSH hS8
  obtain ⟨w, hwS, hw1⟩ : ∃ w ∈ fixV S, w ≠ 1 := by
    by_contra h
    push Not at h
    have : fixV S = ⊥ := eq_bot_iff.mpr fun v hv => Subgroup.mem_bot.mpr (h v hv)
    rw [this, Subgroup.card_bot] at h4
    norm_num at h4
  have hfpf : ∀ c ∈ Subgroup.center ↥H, c ≠ 1 → ∀ v : V, (c : MulAut V) v = v → v = 1 := by
    intro c hc hc1 v hv
    have hle : Subgroup.zpowers c ≤ Subgroup.center ↥H := Subgroup.zpowers_le.mpr hc
    have hcard : Nat.card (Subgroup.zpowers c) = 3 := by
      have hd : Nat.card (Subgroup.zpowers c) ∣ 3 := hH.center ▸ Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exfalso
        rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
        exact hc1 h
      · exact h
    have heq : Subgroup.zpowers c = Subgroup.center ↥H :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hH.center])
    have hz : zH ∈ Subgroup.zpowers c := by
      rw [heq, hcen]
      exact Subgroup.mem_zpowers zH
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    apply hfp v
    have hv' := (HatA6.mem_fixV_zpowers_iff).mpr hv
    have := hv' ((c : MulAut V) ^ k) (Subgroup.zpow_mem_zpowers _ k)
    rw [← hk, Subgroup.coe_zpow]
    exact this
  obtain ⟨f, -, hf⟩ := Orbit.hatA6_orbits (V := V) (by rw [hH.card]; norm_num)
    (Group.isPerfect_def.1 hH.perf) hH.center hH.quot.some hfpf
  have horb : Nat.card (Orbit.orbitIn H w) = 18 ∨ Nat.card (Orbit.orbitIn H w) = 45 := by
    by_cases h : w ∈ Orbit.orbitIn H f
    · exact Or.inl ((hf w hw1).1 h)
    · exact Or.inr ((hf w hw1).2 h)
  set St := MulAction.stabilizer ↥H w with hSt
  have hos : Nat.card (Orbit.orbitIn H w) * Nat.card St = 1080 := by
    rw [Orbit.orbitIn_eq_orbit, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, ← hH.card_H]
    exact St.index_mul_card
  set P := St.map H.subtype with hP
  have hPcard : Nat.card P = Nat.card St := Subgroup.card_map_of_injective H.subtype_injective
  have hmemP : ∀ p : MulAut V, p ∈ P ↔ p ∈ H ∧ p w = w := by
    intro p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨hpH, hpw⟩
      exact ⟨⟨p, hpH⟩, hpw, rfl⟩
  have hSP : S ≤ P := fun s hs => (hmemP s).mpr ⟨hSH hs, hwS s hs⟩
  have h8 : 8 ∣ Nat.card P := hS8 ▸ Subgroup.card_dvd_of_le hSP
  have hP24 : Nat.card P = 24 := by
    rw [hPcard] at h8 ⊢
    rcases horb with h | h <;> rw [h] at hos <;> omega
  refine ⟨P, hSP, fun p hp => ((hmemP p).mp hp).1, hP24, fun p hp v hv => ?_, fun p hp hpc => ?_⟩
  · obtain ⟨hpH, hpw⟩ := (hmemP p).mp hp
    have hpz : ∀ b ∈ Subgroup.zpowers p, b * zH = zH * b := by
      intro b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_left (MS93.S38H.HatMod.comm_z_of_mem hcen hpH) m).eq
    have hSz : ∀ s ∈ S, s * zH = zH * s := fun s hs =>
      MS93.S38H.HatMod.comm_z_of_mem hcen (hSH hs)
    set Qs := fixV S ⊓ fixV (Subgroup.zpowers p) with hQs
    have hzQs : ∀ u ∈ Qs, (zH : MulAut V) u ∈ Qs := fun u hu =>
      ⟨MS93.S38H.HatMod.z_mem_fixV hSz hu.1, MS93.S38H.HatMod.z_mem_fixV hpz hu.2⟩
    have hwQs : w ∈ Qs := ⟨hwS, (HatA6.mem_fixV_zpowers_iff).mpr hpw⟩
    have hle : Qs ≤ fixV S := inf_le_left
    have heq : Qs = fixV S := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [h4]
      rcases HatA6.card_cases_of_inv hH.card h3 hfp hzQs with h | h | h | h
      · exfalso
        rw [Subgroup.card_eq_one] at h
        rw [h, Subgroup.mem_bot] at hwQs
        exact hw1 hwQs
      · omega
      · omega
      · omega
    rw [← heq] at hv
    exact (HatA6.mem_fixV_zpowers_iff).mp hv.2
  · obtain ⟨hpH, hpw⟩ := (hmemP p).mp hp
    by_contra hp1
    have hc : (⟨p, hpH⟩ : ↥H) ∈ Subgroup.center ↥H :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hpc y y.2).symm
    exact hw1 (hfpf _ hc (fun h => hp1 (congrArg Subtype.val h)) w hpw)

end HatModule

section A6Lat


theorem lat6_eq_ch615 : Even6.cert.tGens :: Even6.cert.lat =
    [Even6.tGens, Even6.L1, Even6.L2, Even6.L3] := rfl

theorem card_L1_ch615 : Nat.card ↥(Subgroup.closure {g | g ∈ Even6.L1}) = 24 := by
  have h := Even6.cert.card_member_idx (rawIsEnc 6) (Even6.cert.closedOK_of_check Even6.cert_check)
    (Even6.cert.sizesOK_of_check Even6.cert_check) 1 (by rw [lat6_eq_ch615]; simp)
  have hL : (Even6.cert.tGens :: Even6.cert.lat)[1]'(by rw [lat6_eq_ch615]; simp) = Even6.L1 := by
    simp [lat6_eq_ch615]
  rw [hL] at h
  rw [h]
  rfl

theorem card_L2_ch615 : Nat.card ↥(Subgroup.closure {g | g ∈ Even6.L2}) = 24 := by
  have h := Even6.cert.card_member_idx (rawIsEnc 6) (Even6.cert.closedOK_of_check Even6.cert_check)
    (Even6.cert.sizesOK_of_check Even6.cert_check) 2 (by rw [lat6_eq_ch615]; simp)
  have hL : (Even6.cert.tGens :: Even6.cert.lat)[2]'(by rw [lat6_eq_ch615]; simp) = Even6.L2 := by
    simp [lat6_eq_ch615]
  rw [hL] at h
  rw [h]
  rfl

theorem card_D6_ch615 : Nat.card ↥Even6.D = 8 := by
  have h := Even6.cert.card_member_idx (rawIsEnc 6) (Even6.cert.closedOK_of_check Even6.cert_check)
    (Even6.cert.sizesOK_of_check Even6.cert_check) 0 (by rw [lat6_eq_ch615]; simp)
  have hL : (Even6.cert.tGens :: Even6.cert.lat)[0]'(by rw [lat6_eq_ch615]; simp) =
      Even6.tGens := by
    simp [lat6_eq_ch615]
  rw [hL] at h
  rw [h]
  rfl

theorem D_le_L1_ch615 : Even6.D ≤ Subgroup.closure {g | g ∈ Even6.L1} :=
  Subgroup.closure_mono fun g hg => by
    simp only [Set.mem_ofPred_eq, Even6.tGens, Even6.L1, List.mem_cons, List.not_mem_nil,
      or_false] at hg ⊢
    rcases hg with rfl | rfl <;> simp

theorem D_le_L2_ch615 : Even6.D ≤ Subgroup.closure {g | g ∈ Even6.L2} :=
  Subgroup.closure_mono fun g hg => by
    simp only [Set.mem_ofPred_eq, Even6.tGens, Even6.L2, List.mem_cons, List.not_mem_nil,
      or_false] at hg ⊢
    rcases hg with rfl | rfl <;> simp

theorem over6_ch615 {Y : Subgroup (Perm (Fin 6))} (hDY : Even6.D ≤ Y)
    (hYA : Y ≤ alternatingGroup (Fin 6)) :
    Y = Even6.D ∨ Y = Subgroup.closure {g | g ∈ Even6.L1} ∨
      Y = Subgroup.closure {g | g ∈ Even6.L2} ∨ Y = alternatingGroup (Fin 6) := by
  have hYM : Y ≤ Subgroup.closure {g | g ∈ Even6.cert.mGens} := by
    rw [show Even6.cert.mGens = Even6.mGens from rfl, Even6.closure_mGens]
    exact hYA
  obtain ⟨Lj, hLj, hYL⟩ := Even6.cert.overgroups (rawIsEnc 6) Even6.cert_check Y hDY hYM
  rw [lat6_eq_ch615] at hLj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hLj
  rcases hLj with rfl | rfl | rfl | rfl
  · exact Or.inl hYL
  · exact Or.inr (Or.inl hYL)
  · exact Or.inr (Or.inr (Or.inl hYL))
  · right; right; right
    have hc3 := Even6.cert.card_member_idx (rawIsEnc 6)
      (Even6.cert.closedOK_of_check Even6.cert_check)
      (Even6.cert.sizesOK_of_check Even6.cert_check) 3 (by rw [lat6_eq_ch615]; simp)
    have hL3 : (Even6.cert.tGens :: Even6.cert.lat)[3]'(by rw [lat6_eq_ch615]; simp) =
        Even6.L3 := by
      simp [lat6_eq_ch615]
    rw [hL3] at hc3
    have hcard : Nat.card ↥Y = 360 := by
      rw [hYL, hc3]
      rfl
    exact Subgroup.eq_of_le_of_card_ge hYA (by rw [hcard, Even6.card_alt])

theorem eq_of_gen6_ch615 {Y₁ Y₂ Y₃ : Subgroup (Perm (Fin 6))}
    (h1 : Y₁ = Even6.D ∨ Y₁ = Subgroup.closure {g | g ∈ Even6.L1} ∨
      Y₁ = Subgroup.closure {g | g ∈ Even6.L2})
    (h2 : Y₂ = Even6.D ∨ Y₂ = Subgroup.closure {g | g ∈ Even6.L1} ∨
      Y₂ = Subgroup.closure {g | g ∈ Even6.L2})
    (h3 : Y₃ = Subgroup.closure {g | g ∈ Even6.L1} ∨ Y₃ = Subgroup.closure {g | g ∈ Even6.L2})
    (hgen : alternatingGroup (Fin 6) ≤ Y₁ ⊔ Y₂) : Y₁ = Y₃ ∨ Y₂ = Y₃ := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne1, hne2⟩ := hne
  have hsmall : ∀ L : Subgroup (Perm (Fin 6)), Nat.card ↥L = 24 → Y₁ ≤ L → Y₂ ≤ L → False := by
    intro L hL h1L h2L
    have := Subgroup.card_le_of_le (hgen.trans (sup_le h1L h2L))
    rw [Even6.card_alt, hL] at this
    omega
  rcases h3 with rfl | rfl
  · refine hsmall _ card_L2_ch615 ?_ ?_
    · rcases h1 with rfl | rfl | rfl
      · exact D_le_L2_ch615
      · exact absurd rfl hne1
      · exact le_rfl
    · rcases h2 with rfl | rfl | rfl
      · exact D_le_L2_ch615
      · exact absurd rfl hne2
      · exact le_rfl
  · refine hsmall _ card_L1_ch615 ?_ ?_
    · rcases h1 with rfl | rfl | rfl
      · exact D_le_L1_ch615
      · exact le_rfl
      · exact absurd rfl hne1
    · rcases h2 with rfl | rfl | rfl
      · exact D_le_L1_ch615
      · exact le_rfl
      · exact absurd rfl hne2

end A6Lat

end CFSG.Quasithin.H13
