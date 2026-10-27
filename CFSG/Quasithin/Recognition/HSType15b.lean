module

public import CFSG.Quasithin.Recognition.HSType15a
public import CFSG.Quasithin.Recognition.HSTypeB6
public import CFSG.Quasithin.Recognition.HSType13a
public import CFSG.Quasithin.Recognition.L34AmalgamParabolic

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam

variable {G : Type*} [Group G]

theorem spV_add_self : ∀ v : SpV, v + v = 0 := by decide

theorem zmod2_eq_zero_or_one : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide

theorem card_InV2m : Fintype.card {v : SpV // InV2m v} = 4 := by
  rw [Fintype.card_subtype]
  decide

theorem card_InC0m : Fintype.card {v : SpV // InC0m v} = 4 := by
  rw [Fintype.card_subtype]
  decide

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

namespace S6Model

variable (M : S6Model z s)

theorem Φ_mul_self (v : SpV) : M.Φ v * M.Φ v = 1 := by
  rw [← M.add, spV_add_self, M.Φ_zero]

theorem Φ_inv (v : SpV) : (M.Φ v)⁻¹ = M.Φ v :=
  inv_eq_of_mul_eq_one_right (M.Φ_mul_self v)

theorem Φ_smul (e : ZMod 2) (v : SpV) : M.Φ (e • v) = 1 ∨ M.Φ (e • v) = M.Φ v := by
  rcases zmod2_eq_zero_or_one e with rfl | rfl
  · left
    rw [zero_smul, M.Φ_zero]
  · right
    rw [one_smul]

theorem Φ_eq_one {v : SpV} (h : M.Φ v = 1) : v = 0 :=
  M.inj (h.trans M.Φ_zero.symm)

theorem conj_mem_hsB_of_mem {x b : G} (hx : x ∈ hsNB z s) (hb : b ∈ hsB z s) :
    x * b * x⁻¹ ∈ hsB z s :=
  (Subgroup.mem_normalizer_iff.mp hx b).mp hb

theorem act' {x : G} (hx : x ∈ hsNB z s) (v : SpV) :
    x * M.Φ v * x⁻¹ = M.Φ (actS6 (M.π ⟨x, hx⟩) v) :=
  M.act ⟨x, hx⟩ v

@[expose] def pre (X : Subgroup (Equiv.Perm (Fin 6))) : Subgroup G :=
  (X.comap M.π).map (hsNB z s).subtype

theorem mem_pre {X : Subgroup (Equiv.Perm (Fin 6))} {x : G} :
    x ∈ M.pre X ↔ ∃ hx : x ∈ hsNB z s, M.π ⟨x, hx⟩ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hX⟩
    exact ⟨⟨x, hx⟩, hX, rfl⟩

theorem pre_le_hsNB (X : Subgroup (Equiv.Perm (Fin 6))) : M.pre X ≤ hsNB z s :=
  Subgroup.map_subtype_le _

theorem pre_mono {X Y : Subgroup (Equiv.Perm (Fin 6))} (hXY : X ≤ Y) : M.pre X ≤ M.pre Y :=
  Subgroup.map_mono (Subgroup.comap_mono hXY)

theorem hsB_le_hsNB : hsB z s ≤ hsNB z s := Subgroup.le_normalizer

theorem hsB_le_pre (X : Subgroup (Equiv.Perm (Fin 6))) : hsB z s ≤ M.pre X := fun x hx => by
  refine M.mem_pre.mpr ⟨hsB_le_hsNB hx, ?_⟩
  rw [(M.ker ⟨x, hsB_le_hsNB hx⟩).mpr hx]
  exact X.one_mem

theorem π_mem_of_mem_pre {X : Subgroup (Equiv.Perm (Fin 6))} {x : G} (hx : x ∈ M.pre X)
    (hxN : x ∈ hsNB z s) : M.π ⟨x, hxN⟩ ∈ X := by
  obtain ⟨hx', hX⟩ := M.mem_pre.mp hx
  exact hX

theorem card_pre [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) (X : Subgroup (Equiv.Perm (Fin 6))) :
    Nat.card (M.pre X) = 16 * Nat.card X := by
  have hN := h.card_normalizer_hsB hsmemH hsnotK hss hg₀
  rw [pre, Subgroup.card_map_of_injective (hsNB z s).subtype_injective]
  have h1 := (X.comap M.π).card_mul_index
  rw [Subgroup.index_comap_of_surjective X M.π_surj, hN] at h1
  have h2 := X.card_mul_index
  rw [Nat.card_perm, Nat.card_fin] at h2
  have h720 : Nat.factorial 6 = 720 := by decide
  rw [h720] at h2
  have hi : X.index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact absurd h2 (by norm_num)
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  rw [h1, mul_assoc, h2]
  norm_num

@[expose] def V2 : Subgroup G where
  carrier := {x | ∃ v, InV2m v ∧ M.Φ v = x}
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, InV2m_add hv hw, M.add v w⟩
  one_mem' := ⟨0, InV2m_zero, M.Φ_zero⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, (M.Φ_inv v).symm⟩

theorem mem_V2 {x : G} : x ∈ M.V2 ↔ ∃ v, InV2m v ∧ M.Φ v = x := Iff.rfl

theorem Φ_mem_V2 {v : SpV} (hv : InV2m v) : M.Φ v ∈ M.V2 := ⟨v, hv, rfl⟩

theorem InV2m_of_Φ_mem_V2 {v : SpV} (hv : M.Φ v ∈ M.V2) : InV2m v := by
  obtain ⟨w, hw, hwv⟩ := hv
  rw [← M.inj hwv]
  exact hw

theorem V2_le_hsB : M.V2 ≤ hsB z s := by
  rintro _ ⟨v, -, rfl⟩
  exact M.mem v

theorem z_mem_V2 : z ∈ M.V2 := ⟨spE 0, InV2m_spE0, M.e0⟩

theorem V2_le_Q : M.V2 ≤ hsQ z := by
  rintro _ ⟨v, hv, rfl⟩
  exact (M.mem_Q_iff v).mpr (spForm_spE0_of_InV2m v hv)

theorem card_V2 : Nat.card M.V2 = 4 := by
  rw [← card_InV2m, ← Nat.card_eq_fintype_card]
  refine (Nat.card_congr (Equiv.ofBijective (fun v : {v : SpV // InV2m v} =>
    (⟨M.Φ v, v, v.2, rfl⟩ : M.V2)) ⟨fun v w hvw => ?_, fun x => ?_⟩)).symm
  · exact Subtype.ext (M.inj (congrArg Subtype.val hvw))
  · obtain ⟨v, hv, hvx⟩ := x.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvx⟩

@[expose] def C0m : Subgroup G where
  carrier := {x | ∃ v, InC0m v ∧ M.Φ v = x}
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, InC0m_add hv hw, M.add v w⟩
  one_mem' := ⟨0, InC0m_zero, M.Φ_zero⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, (M.Φ_inv v).symm⟩

theorem C0m_le_hsB : M.C0m ≤ hsB z s := by
  rintro _ ⟨v, -, rfl⟩
  exact M.mem v

theorem card_C0m : Nat.card M.C0m = 4 := by
  rw [← card_InC0m, ← Nat.card_eq_fintype_card]
  refine (Nat.card_congr (Equiv.ofBijective (fun v : {v : SpV // InC0m v} =>
    (⟨M.Φ v, v, v.2, rfl⟩ : M.C0m)) ⟨fun v w hvw => ?_, fun x => ?_⟩)).symm
  · exact Subtype.ext (M.inj (congrArg Subtype.val hvw))
  · obtain ⟨v, hv, hvx⟩ := x.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvx⟩

theorem V2_inf_C0m : M.V2 ⊓ M.C0m = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x ⟨⟨v, hv, hvx⟩, ⟨w, hw, hwx⟩⟩ => ?_
  rw [← hwx] at hvx
  have hvw := M.inj hvx
  rw [← hwx, ← hvw, eq_zero_of_InC0m_InV2m v (hvw ▸ hw) hv, M.Φ_zero]

theorem exists_setting_V2 [Finite G] (h : HSSetting z V) :
    ∃ V' : Subgroup G, HSSetting z V' ∧ M.V2 ≤ V' := by
  set v₁ := M.Φ (spE 3) with hv₁
  have hv₁Q : v₁ ∈ hsQ z := M.V2_le_Q (M.Φ_mem_V2 InV2m_spE3)
  have hv₁2 : v₁ * v₁ = 1 := M.Φ_mul_self _
  have hv₁1 : v₁ ≠ 1 := fun h1 => absurd (M.Φ_eq_one h1) (by decide)
  have hv₁z : v₁ ≠ z := fun h1 => absurd (M.inj (h1.trans M.e0.symm)) (by decide)
  have hv₁Z : v₁ ∉ hsZQ z := fun hZ => hv₁z (h.eq_z_of_mem_ZQ hZ hv₁2 hv₁1)
  obtain ⟨v, hvV, hvz⟩ := h.exists_mem_V_not_mem_zpowers
  have hvQ : v ∈ hsQ z := h.two.le hvV
  have hv2 : v * v = 1 := h.mul_self_of_mem_V hvV
  have hvZ : v ∉ hsZQ z := fun hZ => by
    rcases h.eq_one_or_z_of_mem_V_ZQ hvV hZ with e | e
    · exact hvz (e ▸ (Subgroup.zpowers z).one_mem)
    · exact hvz (e ▸ Subgroup.mem_zpowers z)
  obtain ⟨k, hkK, hk⟩ := h.K_transitive hv₁Q hv₁2 hv₁Z hvQ hv2 hvZ
  have hc : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hkK.1
  have hkz : k⁻¹ * z * k⁻¹⁻¹ = z := by
    calc k⁻¹ * z * k⁻¹⁻¹ = k⁻¹ * (z * k) := by group
      _ = k⁻¹ * (k * z) := by rw [← hc]
      _ = z := by group
  refine ⟨V.map (MulAut.conj k⁻¹).toMonoidHom, hkz ▸ h.conj k⁻¹, ?_⟩
  have hzV' : z ∈ V.map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [mem_map_conj_iff, inv_inv, hc, mul_inv_cancel_right]
    exact h.mem_V
  have hv₁V' : v₁ ∈ V.map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [mem_map_conj_iff, inv_inv, hk]
    exact hvV
  rintro _ ⟨w, hw, rfl⟩
  rcases InV2m_cases w hw with rfl | rfl | rfl | rfl
  · rw [M.Φ_zero]
    exact Subgroup.one_mem _
  · rw [M.e0]
    exact hzV'
  · exact hv₁V'
  · rw [M.add, M.e0]
    exact Subgroup.mul_mem _ hzV' hv₁V'

abbrev NN : Subgroup G := M.pre stabS

theorem mem_NN_of_π {x : G} (hxN : x ∈ hsNB z s) (hσ : M.π ⟨x, hxN⟩ ∈ stabS) : x ∈ M.NN :=
  M.mem_pre.mpr ⟨hxN, hσ⟩

theorem NN_le_normalizer : M.NN ≤ Subgroup.normalizer (M.V2 : Set G) := by
  intro x hx
  obtain ⟨hxN, hσ⟩ := M.mem_pre.mp hx
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hy
    rw [M.act' hxN w]
    exact M.Φ_mem_V2 (hσ w hw)
  · have hyB : y ∈ hsB z s := by
      have := conj_mem_hsB_of_mem ((hsNB z s).inv_mem hxN) (M.V2_le_hsB hy)
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this
    obtain ⟨w, rfl⟩ := M.surj y hyB
    have hw : InV2m (actS6 (M.π ⟨x, hxN⟩) w) := by
      rw [M.act' hxN w] at hy
      exact M.InV2m_of_Φ_mem_V2 hy
    refine M.Φ_mem_V2 ?_
    have hσ' : (M.π ⟨x, hxN⟩)⁻¹ ∈ stabS := stabS.inv_mem hσ
    have := hσ' _ hw
    rwa [← actS6_mul, inv_mul_cancel, actS6_one] at this

theorem mem_NN_of_normalizes {x : G} (hxN : x ∈ hsNB z s)
    (hxV : x ∈ Subgroup.normalizer (M.V2 : Set G)) : x ∈ M.NN := by
  refine M.mem_pre.mpr ⟨hxN, fun w hw => ?_⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hxV (M.Φ w)).mp (M.Φ_mem_V2 hw)
  rw [M.act' hxN w] at h1
  exact M.InV2m_of_Φ_mem_V2 h1

theorem card_NN [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) : Nat.card M.NN = 768 := by
  show Nat.card ↥(M.pre stabS) = 768
  rw [M.card_pre h hsmemH hsnotK hss hg₀, card_stabS]

theorem mem_pre_fixS_of_centralizes {x : G} (hxN : x ∈ hsNB z s)
    (hxC : x ∈ Subgroup.centralizer (M.V2 : Set G)) : x ∈ M.pre fixS := by
  refine M.mem_pre.mpr ⟨hxN, fun w hw => ?_⟩
  have h1 : x * M.Φ w * x⁻¹ = M.Φ w := by
    rw [← Subgroup.mem_centralizer_iff.mp hxC _ (M.Φ_mem_V2 hw), mul_inv_cancel_right]
  rw [M.act' hxN w] at h1
  exact M.inj h1

theorem centralizes_of_mem_pre_fixS {x : G} (hx : x ∈ M.pre fixS) :
    x ∈ Subgroup.centralizer (M.V2 : Set G) := by
  obtain ⟨hxN, hσ⟩ := M.mem_pre.mp hx
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  obtain ⟨w, hw, rfl⟩ := hy
  have h1 := M.act' hxN w
  rw [hσ w hw] at h1
  calc M.Φ w * x = x * M.Φ w * x⁻¹ * x := by rw [h1]
    _ = x * M.Φ w := by group

theorem card_normalizer_V2 [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    Nat.card ↥(Subgroup.normalizer (M.V2 : Set G)) = 1536 := by
  obtain ⟨V', h', hV'⟩ := M.exists_setting_V2 h
  have hR : Nat.card ↥(Subgroup.centralizer (M.V2 : Set G)) = 256 := by
    rw [h'.centralizer_V2_eq hV' M.card_V2 M.z_mem_V2, h'.card_R2 hV' M.card_V2]
  set R := Subgroup.centralizer (M.V2 : Set G) with hRdef
  have hNNR : M.NN ⊓ R = M.pre fixS := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hxR⟩ := hx
      exact M.mem_pre_fixS_of_centralizes (M.pre_le_hsNB _ hx1) hxR
    · intro x hx
      exact ⟨M.pre_mono fixS_le_stabS hx, M.centralizes_of_mem_pre_fixS hx⟩
  have hNN := M.card_NN h hsmemH hsnotK hss hg₀
  have hfix : Nat.card ↥(M.pre fixS) = 128 := by
    rw [M.card_pre h hsmemH hsnotK hss hg₀, card_fixS]
  have hNNle : M.NN ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun y => by
      have hxV := M.NN_le_normalizer hx
      constructor
      · intro hy
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have hv' : x⁻¹ * v * x ∈ M.V2 := by
          have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hxV) v).mp hv
          rwa [inv_inv] at this
        have hc := Subgroup.mem_centralizer_iff.mp hy _ hv'
        calc v * (x * y * x⁻¹) = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
          _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [hc]
          _ = x * y * x⁻¹ * v := by group
      · intro hy
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have hv' : x * v * x⁻¹ ∈ M.V2 := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
        have hc := Subgroup.mem_centralizer_iff.mp hy _ hv'
        calc v * y = x⁻¹ * ((x * v * x⁻¹) * (x * y * x⁻¹)) * x := by group
          _ = x⁻¹ * ((x * y * x⁻¹) * (x * v * x⁻¹)) * x := by rw [hc]
          _ = y * v := by group
  have hsup : Subgroup.normalizer (M.V2 : Set G) = M.NN ⊔ R := by
    refine le_antisymm (fun m hm => ?_) (sup_le M.NN_le_normalizer
      (Subgroup.centralizer_le_normalizer _))
    have hmz := (Subgroup.mem_normalizer_iff.mp hm z).mp M.z_mem_V2
    have hm3 := (Subgroup.mem_normalizer_iff.mp hm (M.Φ (spE 3))).mp (M.Φ_mem_V2 InV2m_spE3)
    obtain ⟨a, ha, hae⟩ := hmz
    obtain ⟨b, hb, hbe⟩ := hm3
    have ha0 : a ≠ 0 := fun h0 => by
      rw [h0, M.Φ_zero] at hae
      have : z = 1 := by
        calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
          _ = 1 := by rw [← hae]; group
      exact h.z_ne_one this
    have hb0 : b ≠ 0 := fun h0 => by
      rw [h0, M.Φ_zero] at hbe
      have : M.Φ (spE 3) = 1 := by
        calc M.Φ (spE 3) = m⁻¹ * (m * M.Φ (spE 3) * m⁻¹) * m := by group
          _ = 1 := by rw [← hbe]; group
      exact absurd (M.Φ_eq_one this) (by decide)
    have hab : a ≠ b := fun he => by
      rw [he, hbe] at hae
      have : M.Φ (spE 3) = z := mul_left_cancel (mul_right_cancel hae)
      exact absurd (M.inj (this.trans M.e0.symm)) (by decide)
    obtain ⟨σ, hσ, hσa, hσb⟩ := exists_stabS_map a b ⟨ha, hb, ha0, hb0, hab⟩
    obtain ⟨⟨n, hnN⟩, hn⟩ := M.π_surj σ
    have hnNN : n ∈ M.NN := M.mem_NN_of_π hnN (hn ▸ hσ)
    have hnz : n * z * n⁻¹ = m * z * m⁻¹ := by
      calc n * z * n⁻¹ = n * M.Φ (spE 0) * n⁻¹ := by rw [M.e0]
        _ = M.Φ a := by rw [M.act' hnN, hn, hσa]
        _ = m * z * m⁻¹ := hae
    have hn3 : n * M.Φ (spE 3) * n⁻¹ = m * M.Φ (spE 3) * m⁻¹ := by
      rw [M.act' hnN, hn, hσb, hbe]
    have hcz : n⁻¹ * m * z = z * (n⁻¹ * m) := by
      calc n⁻¹ * m * z = n⁻¹ * (m * z * m⁻¹) * m := by group
        _ = n⁻¹ * (n * z * n⁻¹) * m := by rw [hnz]
        _ = z * (n⁻¹ * m) := by group
    have hc3 : n⁻¹ * m * M.Φ (spE 3) = M.Φ (spE 3) * (n⁻¹ * m) := by
      calc n⁻¹ * m * M.Φ (spE 3) = n⁻¹ * (m * M.Φ (spE 3) * m⁻¹) * m := by group
        _ = n⁻¹ * (n * M.Φ (spE 3) * n⁻¹) * m := by rw [hn3]
        _ = M.Φ (spE 3) * (n⁻¹ * m) := by group
    have hR' : n⁻¹ * m ∈ R := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      obtain ⟨w, hw, rfl⟩ := hy
      rcases InV2m_cases w hw with rfl | rfl | rfl | rfl
      · rw [M.Φ_zero, one_mul, mul_one]
      · rw [M.e0]
        exact hcz.symm
      · exact hc3.symm
      · rw [M.add, M.e0]
        calc z * M.Φ (spE 3) * (n⁻¹ * m) = z * (n⁻¹ * m * M.Φ (spE 3)) := by
              rw [mul_assoc, hc3]
          _ = n⁻¹ * m * (z * M.Φ (spE 3)) := by rw [← mul_assoc, ← hcz, mul_assoc]
    have := Subgroup.mul_mem_sup hnNN hR'
    rwa [mul_inv_cancel_left] at this
  have hp := card_sup_mul_card_inf_of_le_normalizer hNNle
  rw [hNNR, hfix, hNN, hR] at hp
  rw [hsup]
  omega

theorem conj_mem_NN [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g x : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hx : x ∈ M.NN) : g * x * g⁻¹ ∈ M.NN := by
  set M₂ := Subgroup.normalizer (M.V2 : Set G) with hM₂
  have hle := M.NN_le_normalizer
  have hidx : (M.NN.subgroupOf M₂).index = 2 := by
    have h1 := (M.NN.subgroupOf M₂).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      M.card_NN h hsmemH hsnotK hss hg₀, M.card_normalizer_V2 h hsmemH hsnotK hss hg₀] at h1
    omega
  have hn := Subgroup.normal_of_index_eq_two hidx
  have := hn.conj_mem ⟨x, hle hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.mp this

abbrev RX : Subgroup G := M.pre lam0

theorem exists_x0 : ∃ x₀ : G, ∃ hx₀ : x₀ ∈ hsNB z s, M.π ⟨x₀, hx₀⟩ = σS0 := by
  obtain ⟨⟨x₀, hx₀⟩, hπ⟩ := M.π_surj σS0
  exact ⟨x₀, hx₀, hπ⟩

@[expose] def cubes : Set G := {x | x ∈ M.NN ∧ x ^ 3 = 1}

include M in
theorem mul_self_of_mem_hsB {b : G} (hb : b ∈ hsB z s) : b * b = 1 := by
  obtain ⟨u, rfl⟩ := M.surj b hb
  exact M.Φ_mul_self u

theorem exists_cube_lift {τ : Equiv.Perm (Fin 6)} (hτ : τ ∈ stabS) (hτ3 : τ ^ 3 = 1) :
    ∃ x : G, ∃ hx : x ∈ hsNB z s, x ∈ M.cubes ∧ M.π ⟨x, hx⟩ = τ := by
  obtain ⟨n, hn⟩ := M.π_surj τ
  have hn3 : ((n ^ 3 : ↥(hsNB z s)) : G) ∈ hsB z s :=
    (M.ker (n ^ 3)).mp (by rw [map_pow, hn, hτ3])
  have hn6 : (n : G) ^ 12 = 1 := by
    have e := M.mul_self_of_mem_hsB hn3
    rw [Subgroup.coe_pow] at e
    calc (n : G) ^ 12 = ((n : G) ^ 3 * (n : G) ^ 3) ^ 2 := by group
      _ = 1 := by rw [e, one_pow]
  have hπ : M.π (n ^ 4) = τ := by
    rw [map_pow, hn, show τ ^ 4 = τ ^ 3 * τ by group, hτ3, one_mul]
  refine ⟨((n ^ 4 : ↥(hsNB z s)) : G), (n ^ 4).2, ⟨M.mem_NN_of_π (n ^ 4).2 ?_, ?_⟩, hπ⟩
  · rw [hπ]
    exact hτ
  · rw [Subgroup.coe_pow, ← pow_mul]
    exact hn6

theorem cubes_subset_RX : M.cubes ⊆ M.RX := by
  rintro x ⟨hx, hx3⟩
  obtain ⟨hxN, hσ⟩ := M.mem_pre.mp hx
  refine M.mem_pre.mpr ⟨hxN, mem_lamS_of_pow_three _ hσ ?_, hσ⟩
  have e : (⟨x, hxN⟩ : ↥(hsNB z s)) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hx3)
  rw [← map_pow, e, map_one]

theorem hsB_le_closure_cubes : hsB z s ≤ Subgroup.closure M.cubes := by
  intro b hb
  obtain ⟨x₀, hx₀, hc, hπ⟩ := M.exists_cube_lift σS0_mem.2 σS0_pow_three
  obtain ⟨u, rfl⟩ := M.surj b hb
  obtain ⟨w, hw⟩ := exists_add_actS6_σS0 u
  have hwNN : M.Φ w ∈ M.NN := M.hsB_le_pre stabS (M.mem w)
  have hconj : M.Φ w * x₀ * (M.Φ w)⁻¹ ∈ M.cubes := by
    refine ⟨M.NN.mul_mem (M.NN.mul_mem hwNN hc.1) (M.NN.inv_mem hwNN), ?_⟩
    rw [conj_pow, hc.2, mul_one, mul_inv_cancel]
  have e : M.Φ u = M.Φ w * x₀ * (M.Φ w)⁻¹ * x₀⁻¹ := by
    have h1 := M.act' hx₀ w
    rw [hπ] at h1
    rw [← hw, M.add, ← h1, M.Φ_inv]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure hconj)
    (Subgroup.inv_mem _ (Subgroup.subset_closure hc))

theorem mem_closure_cubes_of_π {y x : G} (hyN : y ∈ hsNB z s) (hxN : x ∈ hsNB z s)
    (hx : x ∈ Subgroup.closure M.cubes) (he : M.π ⟨y, hyN⟩ = M.π ⟨x, hxN⟩) :
    y ∈ Subgroup.closure M.cubes := by
  have hmem : y * x⁻¹ ∈ hsNB z s := (hsNB z s).mul_mem hyN ((hsNB z s).inv_mem hxN)
  have hB : y * x⁻¹ ∈ hsB z s := by
    refine (M.ker ⟨_, hmem⟩).mp ?_
    have e : (⟨y * x⁻¹, hmem⟩ : ↥(hsNB z s)) = ⟨y, hyN⟩ * ⟨x, hxN⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, he, mul_inv_cancel]
  have := Subgroup.mul_mem _ (M.hsB_le_closure_cubes hB) hx
  rwa [inv_mul_cancel_right] at this

theorem RX_eq_closure : M.RX = Subgroup.closure M.cubes := by
  refine le_antisymm (fun y hy => ?_) ((Subgroup.closure_le _).mpr M.cubes_subset_RX)
  obtain ⟨hyN, hρ⟩ := M.mem_pre.mp hy
  rcases pow_three_or_of_mem_lam0 _ hρ with h3 | h3
  · obtain ⟨x, hxN, hx, hπ⟩ := M.exists_cube_lift hρ.2 h3
    exact M.mem_closure_cubes_of_π hyN hxN (Subgroup.subset_closure hx) hπ.symm
  · have hτ : σS0⁻¹ * M.π ⟨y, hyN⟩ ∈ stabS :=
      stabS.mul_mem (stabS.inv_mem σS0_mem.2) hρ.2
    obtain ⟨x₁, hx₁N, hx₁, hπ₁⟩ := M.exists_cube_lift hτ h3
    obtain ⟨x₀, hx₀N, hx₀, hπ₀⟩ := M.exists_cube_lift σS0_mem.2 σS0_pow_three
    have hmem : x₀ * x₁ ∈ hsNB z s := (hsNB z s).mul_mem hx₀N hx₁N
    refine M.mem_closure_cubes_of_π hyN hmem (Subgroup.mul_mem _ (Subgroup.subset_closure hx₀)
      (Subgroup.subset_closure hx₁)) ?_
    have e : (⟨x₀ * x₁, hmem⟩ : ↥(hsNB z s)) = ⟨x₀, hx₀N⟩ * ⟨x₁, hx₁N⟩ := rfl
    rw [e, map_mul, hπ₀, hπ₁, mul_inv_cancel_left]

theorem conj_mem_RX [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g x : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hx : x ∈ M.RX) : g * x * g⁻¹ ∈ M.RX := by
  rw [M.RX_eq_closure] at hx ⊢
  have hle : Subgroup.closure M.cubes ≤
      (Subgroup.closure M.cubes).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y ⟨hy, hy3⟩
    refine Subgroup.subset_closure ⟨M.conj_mem_NN h hsmemH hsnotK hss hg₀ hg hy, ?_⟩
    show (g * y * g⁻¹) ^ 3 = 1
    rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  exact hle hx

section Second

variable [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
  (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s)

include h hsmemH hsnotK hss hg₀ in
theorem exists_g : ∃ g ∈ Subgroup.normalizer (M.V2 : Set G), g ∉ M.NN := by
  by_contra hne
  push Not at hne
  have := Subgroup.card_le_of_le (fun x hx => hne x hx :
    Subgroup.normalizer (M.V2 : Set G) ≤ M.NN)
  rw [M.card_normalizer_V2 h hsmemH hsnotK hss hg₀, M.card_NN h hsmemH hsnotK hss hg₀] at this
  omega

variable {g : G} (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN)

omit [Finite G] in
include hg in
theorem conj_inv_mem_V2 {x : G} (hx : x ∈ M.V2) : g⁻¹ * x * g ∈ M.V2 := by
  have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) x).mp hx
  rwa [inv_inv] at this

include h hsmemH hsnotK hss hg₀ hg in
theorem hsB'_le_RX : (hsB z s).map (MulAut.conj g).toMonoidHom ≤ M.RX := by
  rintro _ ⟨b, hb, rfl⟩
  exact M.conj_mem_RX h hsmemH hsnotK hss hg₀ hg (M.hsB_le_pre lam0 hb)

omit [Finite G] in
include hg hgNN in
theorem hsB'_ne : (hsB z s).map (MulAut.conj g).toMonoidHom ≠ hsB z s := by
  intro he
  apply hgNN
  have hgN : g ∈ hsNB z s := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have hy' : g * y * g⁻¹ ∈ (hsB z s).map (MulAut.conj g).toMonoidHom := by
        rw [mem_map_conj_iff, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
        exact hy
      rwa [he] at hy'
    · have hy' : g * y * g⁻¹ ∈ (hsB z s).map (MulAut.conj g).toMonoidHom := by
        rw [he]
        exact hy
      rwa [mem_map_conj_iff, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at hy'
  exact M.mem_NN_of_normalizes hgN hg

omit [Finite G] in
include hg in
theorem V2_le_hsB' : M.V2 ≤ (hsB z s).map (MulAut.conj g).toMonoidHom := fun x hx => by
  rw [mem_map_conj_iff]
  exact M.V2_le_hsB (M.conj_inv_mem_V2 hg hx)

include h hsmemH hsnotK hss hg₀ hg in
theorem conj_mem_hsB'_of_NN {x y : G} (hx : x ∈ M.NN)
    (hy : y ∈ (hsB z s).map (MulAut.conj g).toMonoidHom) :
    x * y * x⁻¹ ∈ (hsB z s).map (MulAut.conj g).toMonoidHom := by
  rw [mem_map_conj_iff] at hy ⊢
  have hx' : g⁻¹ * x * g ∈ M.NN := by
    have := M.conj_mem_NN h hsmemH hsnotK hss hg₀ ((Subgroup.normalizer _).inv_mem hg) hx
    rwa [inv_inv] at this
  have := conj_mem_hsB_of_mem (M.pre_le_hsNB stabS hx') hy
  rwa [show g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * y * x⁻¹) * g by group]
    at this

theorem spV_eq_add_add : ∀ w a b : SpV, w = w + a + b + a + b := by decide

include h hsmemH hsnotK hss hg₀ hg hgNN in
theorem hsB_inf_hsB' : hsB z s ⊓ (hsB z s).map (MulAut.conj g).toMonoidHom = M.V2 := by
  set B' := (hsB z s).map (MulAut.conj g).toMonoidHom with hB'
  refine le_antisymm (fun y ⟨hyB, hyB'⟩ => ?_) (le_inf M.V2_le_hsB (M.V2_le_hsB' hg))
  by_contra hyV
  obtain ⟨v, rfl⟩ := M.surj y hyB
  have hv : ¬ InV2m v := fun hv => hyV (M.Φ_mem_V2 hv)
  obtain ⟨x₀, hx₀, hπ⟩ := M.exists_x0
  have hx₀NN : x₀ ∈ M.NN := M.mem_NN_of_π hx₀ (by rw [hπ]; exact σS0_mem.2)
  have hσv : M.Φ (actS6 σS0 v) ∈ B' := by
    rw [← hπ, ← M.act' hx₀ v]
    exact M.conj_mem_hsB'_of_NN h hsmemH hsnotK hss hg₀ hg hx₀NN hyB'
  have hmem : ∀ u : SpV, M.Φ u ∈ B' → ∀ e : ZMod 2, M.Φ (e • u) ∈ B' := fun u hu e => by
    rcases M.Φ_smul e u with h1 | h1 <;> rw [h1]
    · exact Subgroup.one_mem _
    · exact hu
  have hle : hsB z s ≤ B' := by
    intro b hb
    obtain ⟨w, rfl⟩ := M.surj b hb
    obtain ⟨e₁, e₂, he⟩ := exists_mem_V2m_of_σS0 v hv w
    rw [spV_eq_add_add w (e₁ • v) (e₂ • actS6 σS0 v), M.add, M.add]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (M.V2_le_hsB' hg (M.Φ_mem_V2 he))
      (hmem v hyB' e₁)) (hmem _ hσv e₂)
  apply M.hsB'_ne hg hgNN
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hB', Subgroup.card_map_of_injective (MulAut.conj g).injective]

abbrev C0 (g : G) : Subgroup G := M.C0m.map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem C0_le_hsB' : M.C0 g ≤ (hsB z s).map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_mono M.C0m_le_hsB

omit [Finite G] in
theorem card_C0 : Nat.card (M.C0 g) = 4 := by
  show Nat.card ↥(M.C0m.map (MulAut.conj g).toMonoidHom) = 4
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, M.card_C0m]

include h hsmemH hsnotK hss hg₀ hg hgNN in
theorem C0_inf_hsB : M.C0 g ⊓ hsB z s = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun y ⟨hyC, hyB⟩ => ?_
  have hyV : y ∈ M.V2 := by
    rw [← M.hsB_inf_hsB' h hsmemH hsnotK hss hg₀ hg hgNN]
    exact ⟨hyB, M.C0_le_hsB' hyC⟩
  have h1 : g⁻¹ * y * g ∈ M.V2 ⊓ M.C0m := ⟨M.conj_inv_mem_V2 hg hyV, mem_map_conj_iff.mp hyC⟩
  rw [M.V2_inf_C0m, Subgroup.mem_bot] at h1
  calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

abbrev R : Subgroup G := M.pre kleinS

include h hsmemH hsnotK hss hg₀ hg in
theorem hsB'_le_R : (hsB z s).map (MulAut.conj g).toMonoidHom ≤ M.R := by
  intro y hy
  have hyRX := M.hsB'_le_RX h hsmemH hsnotK hss hg₀ hg hy
  obtain ⟨hyN, hρ⟩ := M.mem_pre.mp hyRX
  refine M.mem_pre.mpr ⟨hyN, mem_kleinS_of_lam0 _ hρ ?_⟩
  have hyy : y * y = 1 := by
    rw [mem_map_conj_iff] at hy
    have hbb := h.hsB_sq hsmemH hsnotK hss hy
    calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [hbb]; group
  rw [← map_mul]
  have e : (⟨y, hyN⟩ : ↥(hsNB z s)) * ⟨y, hyN⟩ = 1 := Subtype.ext hyy
  rw [e, map_one]

include h hsmemH hsnotK hss hg₀ hg hgNN in
theorem hsB_sup_C0 : hsB z s ⊔ M.C0 g = M.R := by
  have hC0R : M.C0 g ≤ M.R := M.C0_le_hsB'.trans (M.hsB'_le_R h hsmemH hsnotK hss hg₀ hg)
  have hC0N : M.C0 g ≤ Subgroup.normalizer (hsB z s : Set G) := hC0R.trans (M.pre_le_hsNB _)
  have hp := card_sup_mul_card_inf_of_le_normalizer hC0N
  rw [M.C0_inf_hsB h hsmemH hsnotK hss hg₀ hg hgNN, Subgroup.card_bot, mul_one, M.card_C0,
    h.card_hsB hsmemH hsnotK hss] at hp
  have hp' : Nat.card ↥(hsB z s ⊔ M.C0 g) = 64 := by
    rw [sup_comm]
    omega
  have hR : Nat.card ↥(M.R) = 64 := by
    show Nat.card ↥(M.pre kleinS) = 64
    rw [M.card_pre h hsmemH hsnotK hss hg₀, card_kleinS]
  exact Subgroup.eq_of_le_of_card_ge (sup_le (M.hsB_le_pre _) hC0R) (hR.trans hp'.symm).le

end Second

end S6Model

end HSSetting

end CFSG.Quasithin.HSType
