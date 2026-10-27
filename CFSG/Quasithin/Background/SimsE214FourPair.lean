module

public import CFSG.Quasithin.Background.SimsE214FourBase
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace E214F

variable {Γ : Type} [Group Γ] [Finite Γ] {X T M V : Subgroup Γ} {g : Γ}

theorem fixed_of_pair (hp : E2.Pair X T M V g) :
    ∀ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V),
      (∀ y ∈ X, y * p * y⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V) → p ∈ V ⊓ B6.conjSub g V := by
  intro p hpP hfix
  have hB := hp.mem_B_of_commutator_mem_Z hpP (fun w hw => hfix w (hp.V_le hw))
  have hpP' : g⁻¹ * p * g ∈ ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) := by
    have := (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P (X.inv_mem hp.mem)) p).mp hpP
    simpa using this
  have hB' := hp.mem_B_of_commutator_mem_Z hpP' (fun w hw => by
    have hgw : g * w * g⁻¹ ∈ B6.conjSub g V := by
      rw [B6.mem_conjSub]
      simpa [mul_assoc] using hw
    have h1 := hfix (g * w * g⁻¹) (hp.conj_le hgw)
    have hc := hp.mem_center h1 (X.inv_mem hp.mem)
    have e1 : w * (g⁻¹ * p * g) * w⁻¹ * (g⁻¹ * p * g)⁻¹ =
        g⁻¹ * (g * w * g⁻¹ * p * (g * w * g⁻¹)⁻¹ * p⁻¹) * g := by group
    rw [e1, ← hc, inv_mul_cancel_right]
    exact h1)
  have hA : p ∈ B6.conjSub g (kerIn M X ⊓ V) := by
    rw [B6.mem_conjSub]
    exact hB'
  rw [← hp.B_inf_A]
  exact ⟨hB, hA⟩

theorem le_sup_kerIn {L : Subgroup Γ} (hL : E2.star M X L = ⊤) : X ≤ L ⊔ kerIn M X := by
  intro x hx
  have h1 : E2P.starMap M X ⟨x, hx⟩ ∈ E2.star M X L := by
    rw [hL]
    exact Subgroup.mem_top _
  rw [E2P.star_def] at h1
  obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp h1
  rw [E2P.starMap, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hlx
  rw [Subgroup.mem_subgroupOf] at hl
  have e1 : x = (l : Γ) * ((l : Γ)⁻¹ * x) := by group
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right (by simpa using hlx))

theorem le_sup_zpowers_sup_kerIn {W : Subgroup Γ} {e : Γ} (hWX : W ≤ X) (heX : e ∈ X)
    (h : E2.star M X W ⊔ Subgroup.zpowers (E2P.starMap M X ⟨e, heX⟩) = ⊤) :
    X ≤ (W ⊔ Subgroup.zpowers e) ⊔ kerIn M X := by
  refine le_sup_kerIn (eq_top_iff.mpr (h ▸ sup_le ?_ ?_))
  · rw [E2P.star_def, E2P.star_def]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X le_sup_left)
  · rw [Subgroup.zpowers_le, E2P.star_def]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers e)))

theorem four_of_gen (hp : E2.Pair X T M V g) (hJ : pCoreOf 2 X = kerIn M X)
    (hN : ∀ N : Subgroup (E2.StarQuot M X), N.Normal → N ≠ ⊥ →
      ∀ z : E2.StarQuot M X, Odd (orderOf z) → z ∈ N)
    {k r : ℕ} (hk : 0 < k) (hr : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r (4 * k))
    (hrX : r ∣ Nat.card (E2.StarQuot M X)) {v e : Γ} (hv : v ∈ V) (he : e ∈ B6.conjSub g V)
    (hgv : E2.star M X V ⊔ Subgroup.zpowers (E2P.starMap M X ⟨e, hp.conj_le he⟩) = ⊤)
    (hge : E2.star M X (B6.conjSub g V) ⊔
      Subgroup.zpowers (E2P.starMap M X ⟨v, hp.V_le hv⟩) = ⊤)
    {Y₁ Y₂ : Subgroup Γ} (hZY : V ⊓ B6.conjSub g V ≤ Y₂) (hY : Y₂ < Y₁)
    (hY₁P : Y₁ ≤ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V))
    (hXY₁ : X ≤ Subgroup.normalizer (Y₁ : Set Γ)) (hXY₂ : X ≤ Subgroup.normalizer (Y₂ : Set Γ)) :
    4 * k ≤ E3.mQuot Y₁ Y₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V) with hPdef
  set Z := V ⊓ B6.conjSub g V with hZdef
  have hJ2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hJX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hPJ : P ≤ pCoreOf 2 X := hp.P_le_pCoreOf
  have hPX : P ≤ X := hPJ.trans hJX
  have hXP : X ≤ Subgroup.normalizer (P : Set Γ) := hp.le_normalizer_P
  have hZc : ∀ z ∈ Z, ∀ y ∈ X, z * y = y * z := fun z hz y hy => hp.mem_center hz hy
  have hPab : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Z := fun p hp' q hq =>
    (hp.commutator_sq_mem_Z hp' hq).1
  have hJc : ∀ y ∈ X, ∀ j ∈ pCoreOf 2 X, y * j * y⁻¹ * j⁻¹ ∈ P := fun y hy j hj =>
    hp.commutator_mem_P_of_mem_pCoreOf hy hj
  have hfixX := fixed_of_pair hp
  have hvX : v ∈ X := hp.V_le hv
  have heX : e ∈ X := hp.conj_le he
  have hgen1 : X ≤ (V ⊔ Subgroup.zpowers e) ⊔ pCoreOf 2 X := by
    rw [hJ]
    exact le_sup_zpowers_sup_kerIn hp.V_le heX hgv
  have hgen2 : X ≤ (B6.conjSub g V ⊔ Subgroup.zpowers v) ⊔ pCoreOf 2 X := by
    rw [hJ]
    exact le_sup_zpowers_sup_kerIn hp.conj_le hvX hge
  have hL1 := fixed_of_sup hJ2 hJX hPJ hXP hZc hPab hJc hfixX
    (sup_le hp.V_le (Subgroup.zpowers_le.mpr heX)) hgen1
  have hL2 := fixed_of_sup hJ2 hJX hPJ hXP hZc hPab hJc hfixX
    (sup_le hp.conj_le (Subgroup.zpowers_le.mpr hvX)) hgen2
  have hCBe : ∀ b ∈ kerIn M X ⊓ V, e * b * e⁻¹ * b⁻¹ ∈ Z → b ∈ Z := by
    intro b hb hbe
    refine hL1 b (Subgroup.mem_sup_left hb) fun l hl => ?_
    have hVF : V ≤ fixModSubgroup X Z hZc b := fun w hw =>
      ⟨hp.V_le hw, by rw [hp.comm hw hb.2, mul_inv_cancel_right, mul_inv_cancel]; exact Z.one_mem⟩
    have heF : Subgroup.zpowers e ≤ fixModSubgroup X Z hZc b :=
      Subgroup.zpowers_le.mpr ⟨heX, hbe⟩
    exact ((sup_le hVF heF) hl).2
  have hCAv : ∀ a ∈ B6.conjSub g (kerIn M X ⊓ V), v * a * v⁻¹ * a⁻¹ ∈ Z → a ∈ Z := by
    intro a ha hav
    refine hL2 a (Subgroup.mem_sup_right ha) fun l hl => ?_
    have haV : a ∈ B6.conjSub g V := (B6.conjSub g).monotone inf_le_right ha
    have hVF : B6.conjSub g V ≤ fixModSubgroup X Z hZc a := fun w hw =>
      ⟨hp.conj_le hw, by
        rw [hp.comm_conj hw haV, mul_inv_cancel_right, mul_inv_cancel]; exact Z.one_mem⟩
    have hvF : Subgroup.zpowers v ≤ fixModSubgroup X Z hZc a :=
      Subgroup.zpowers_le.mpr ⟨hvX, hav⟩
    exact ((sup_le hVF hvF) hl).2
  have hve : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ Z → e * p * e⁻¹ * p⁻¹ ∈ Z → p ∈ Z := by
    intro p hpP hpv hpe
    obtain ⟨b, hb, a, ha, rfl⟩ := hp.mem_P_iff.mp hpP
    have hbX : b ∈ X := hPX (Subgroup.mem_sup_left hb)
    have hva : v * a * v⁻¹ * a⁻¹ ∈ Z := by
      have e1 : v * (b * a) * v⁻¹ * (b * a)⁻¹ = b * (v * a * v⁻¹ * a⁻¹) * b⁻¹ := by
        calc v * (b * a) * v⁻¹ * (b * a)⁻¹ = (v * b) * a * v⁻¹ * a⁻¹ * b⁻¹ := by group
          _ = (b * v) * a * v⁻¹ * a⁻¹ * b⁻¹ := by rw [hp.comm hv hb.2]
          _ = b * (v * a * v⁻¹ * a⁻¹) * b⁻¹ := by group
      rw [e1] at hpv
      have hc := hZc _ hpv b⁻¹ (X.inv_mem hbX)
      have e2 : v * a * v⁻¹ * a⁻¹ = b⁻¹ * (b * (v * a * v⁻¹ * a⁻¹) * b⁻¹) * b := by group
      rw [e2, ← hc, inv_mul_cancel_right]
      exact hpv
    have hbe : e * b * e⁻¹ * b⁻¹ ∈ Z := by
      have haV : a ∈ B6.conjSub g V := (B6.conjSub g).monotone inf_le_right ha
      have hea : e * a = a * e := hp.comm_conj he haV
      have e1 : e * (b * a) * e⁻¹ * (b * a)⁻¹ = e * b * e⁻¹ * b⁻¹ := by
        calc e * (b * a) * e⁻¹ * (b * a)⁻¹ = e * b * (e⁻¹ * (e * a) * e⁻¹) * a⁻¹ * b⁻¹ := by
              group
          _ = e * b * (e⁻¹ * (a * e) * e⁻¹) * a⁻¹ * b⁻¹ := by rw [hea]
          _ = e * b * e⁻¹ * b⁻¹ := by group
      rw [e1] at hpe
      exact hpe
    exact Z.mul_mem (hCBe b hb hbe) (hCAv a ha hva)
  have hv2 : v * v = 1 := by rw [← pow_two]; exact hp.elem.2 v hv
  have he2 : e * e = 1 := by
    have h1 : (g⁻¹ * e * g) * (g⁻¹ * e * g) = 1 := by
      rw [← pow_two]; exact hp.elem.2 _ (B6.mem_conjSub.mp he)
    calc e * e = g * ((g⁻¹ * e * g) * (g⁻¹ * e * g)) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨x, hxz, hxo, hxfpf⟩ :=
    exists_fpf_of_pair hvX heX hv2 he2 (hJ2.to_le hPJ) hPX hXP hZc hve
  have hxX : x ∈ X := Subgroup.zpowers_le.mpr (X.mul_mem hvX heX) hxz
  have hXZ : X ≤ Subgroup.normalizer (Z : Set Γ) := fun y hy =>
    B6.mem_normalizer_of_forall_mem
      (fun z hz => by rw [← hZc z hz y hy, mul_inv_cancel_right]; exact hz)
      (fun z hz => by rw [← hZc z hz y⁻¹ (X.inv_mem hy), inv_mul_cancel_right]; exact hz)
  have hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz => by
    rw [← hZc z hz x hxX, mul_inv_cancel_right]
  have hxY₂ : ∀ y ∈ Y₂, x * y * x⁻¹ ∈ Y₂ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hXY₂ hxX) y).mp hy
  obtain ⟨y₀, hy₀Y₁, hy₀Y₂⟩ := SetLike.exists_of_lt hY
  have hxne : ∃ y ∈ Y₁, x * y * x⁻¹ * y⁻¹ ∉ Y₂ := ⟨y₀, hy₀Y₁, fun h => hy₀Y₂
    (mem_of_commutator_mem hZY (hY.le.trans hY₁P) (hPX.trans hXZ) hxZ hxY₂ hxfpf
      (hY₁P hy₀Y₁) h)⟩
  have hxo' : Odd (orderOf (E2P.starMap M X ⟨x, hxX⟩)) := by
    have h1 : orderOf (E2P.starMap M X ⟨x, hxX⟩) ∣ orderOf (⟨x, hxX⟩ : X) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hxo h1
  have hker : ∀ i ∈ X, (∀ y ∈ Y₁, i * y * i⁻¹ * y⁻¹ ∈ Y₂) → i ∈ kerIn M X := fun i hi hiy =>
    mem_kerIn_of_forall_commutator_mem hp.le_X (hJ ▸ hJ2) hXY₁ hXY₂ hxX hxo
      (fun N hNn hN1 => hN N hNn hN1 _ hxo') hxne hi hiy
  have : Fact r.Prime := ⟨hr.prime⟩
  have hrX' : r ∣ Nat.card X := hrX.trans (by
    show (kerIn M X).relIndex X ∣ Nat.card X
    exact Subgroup.relIndex_dvd_card _ _)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := X) r hrX'
  have hcX : (c : Γ) ∈ X := c.2
  have hcord : orderOf (c : Γ) = r := by rw [Subgroup.orderOf_coe, hc]
  have hr2 : r ≠ 2 := hr.ne_two (by omega)
  have hcJ : (c : Γ) ∉ kerIn M X := by
    intro hcJ
    rw [← hJ] at hcJ
    obtain ⟨n, hn⟩ := hJ2 ⟨c, hcJ⟩
    have h1 : (c : Γ) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hcord] at h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp (hr.prime.dvd_of_dvd_pow h2))
  have hcne : ∃ y ∈ Y₁, (c : Γ) * y * (c : Γ)⁻¹ * y⁻¹ ∉ Y₂ := by
    by_contra hcon
    push Not at hcon
    exact hcJ (hker c hcX hcon)
  obtain ⟨m, hm0, hmdvd, hmle⟩ := exists_dvd_two_pow_sub_one_le hr.prime hr2 hcord
    (hJ2.to_le (hY₁P.trans hPJ)) hY.le ((hY₁P.trans hPX).trans hXY₂) (hXY₁ hcX) (hXY₂ hcX) hcne
  have h4k : 4 * k ∣ m := (hr.dvd_sub_one_iff (by omega) m).mp hmdvd
  exact (Nat.le_of_dvd hm0 h4k).trans hmle

end E214F

end CFSG.Quasithin.SimsE2
