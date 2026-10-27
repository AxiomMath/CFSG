module

public import CFSG.Quasithin.H13.L32AM50j
public import CFSG.Quasithin.H13.L32AM50k
public import CFSG.Quasithin.H13.L32AC40e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative

theorem Alt7.exists_ta_sq_ne_one : ∃ a ∈ taList, a * a ≠ 1 := by
  have h : taList.any (fun a => decide (a * a ≠ 1)) = true := by
    decide +kernel
  exact of_any h

theorem Alt7.card_le_four {P : Subgroup (alternatingGroup (Fin 7))} (hP : ∀ x ∈ P, x * x = 1) :
    Nat.card P ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hP x x.2)⟩
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hdvd : Nat.card P ∣ 2520 := by
    rw [← Alt7.card_alt7]
    exact Subgroup.card_subgroup_dvd_card P
  rw [hn] at hdvd ⊢
  have hn3 : n ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ∣ 2520 := (Nat.pow_dvd_pow 2 h).trans hdvd
    norm_num at this
  by_contra h4
  have hn3' : n = 3 := by
    by_contra h
    have : n ≤ 2 := by omega
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  subst hn3'
  set D : Subgroup (alternatingGroup (Fin 7)) := Alt7.taSub.subgroupOf (alternatingGroup (Fin 7))
    with hD
  have hDR : Alt7.taSub ≤ alternatingGroup (Fin 7) := fun g hg =>
    mem_alternatingGroup.mpr (Alt7.ta_sign g hg)
  have hDc : Nat.card D = 8 := by
    rw [hD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDR).toEquiv, Alt7.card_taSub]
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 3) (hDc.trans (by norm_num))
  have hodd : ∀ X : Subgroup (alternatingGroup (Fin 7)), Nat.card X = 8 → ¬ 2 ∣ X.index := by
    intro X hX
    have h1 := X.card_mul_index
    rw [hX, Alt7.card_alt7] at h1
    rintro ⟨m, hm⟩
    omega
  obtain ⟨h, hh⟩ := exists_conj_map_eq_of_sylow (MonoidHom.id _) Function.surjective_id hP2
    (hodd P (by rw [hn]; norm_num)) hD2 (hodd D hDc)
  obtain ⟨a, ha, ha2⟩ := Alt7.exists_ta_sq_ne_one
  have haD : (⟨a, hDR ha⟩ : alternatingGroup (Fin 7)) ∈ D := Subgroup.mem_subgroupOf.mpr ha
  rw [← hh] at haD
  obtain ⟨_, ⟨p, hp, rfl⟩, hpa⟩ := haD
  apply ha2
  have e : (⟨a, hDR ha⟩ : alternatingGroup (Fin 7)) = h⁻¹ * p * h := by
    rw [← hpa]
    simp
  have hpp := hP p hp
  have e2 : (⟨a, hDR ha⟩ : alternatingGroup (Fin 7)) * ⟨a, hDR ha⟩ = 1 := by
    rw [e]
    calc h⁻¹ * p * h * (h⁻¹ * p * h) = h⁻¹ * (p * p) * h := by group
      _ = 1 := by rw [hpp]; group
  exact congrArg Subtype.val e2

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace TopW

variable {W : Subgroup G} (C : TopW T L V H W) [IsMulCommutative ↥(conjClosure V H)]
include C

omit [Finite G] C in
theorem mk_eq_mk_iff (u u' : ↥(conjClosure V H)) :
    InternalSec.secMk (W.subgroupOf (conjClosure V H)) u =
        InternalSec.secMk (W.subgroupOf (conjClosure V H)) u' ↔ (u : G) * (u' : G)⁻¹ ∈ W := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff, Subgroup.coe_mul,
    Subgroup.coe_inv]

theorem commHom_act_mk (h : ↥H) (u : ↥(conjClosure V H)) :
    A5Mod.commHom (C.act h) (InternalSec.secMk (W.subgroupOf (conjClosure V H)) u) =
      InternalSec.secMk (W.subgroupOf (conjClosure V H))
        (Setup.rho (conjClosure V H) H (le_normalizer_conjClosure V H) h u * u⁻¹) := by
  rw [A5Mod.commHom_apply, C.act_secMk, ← map_inv, ← map_mul]

theorem card_range_le_relIndex {B : Subgroup G} (hBH : B ≤ H) {x : G} (hx : x ∈ B) :
    Nat.card (A5Mod.commHom (C.act ⟨x, hBH hx⟩)).range ≤
      (centralizerMod (fsuV1 T V) (conjClosure V H) B).relIndex (conjClosure V H) := by
  set U := conjClosure V H with hU
  set q := InternalSec.secMk (W.subgroupOf U) with hq
  set Z := (centralizerMod (fsuV1 T V) U B).subgroupOf U with hZ
  have hZf : Z.map q ≤ (A5Mod.commHom (C.act ⟨x, hBH hx⟩)).ker := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : (z : G) ∈ centralizerMod (fsuV1 T V) U B := hz
    have hc := (mem_centralizerMod.mp hz').2.2 x hx
    rw [MonoidHom.mem_ker, hq, C.commHom_act_mk, A6.A6Mod.secMk_eq_one_iff, Subgroup.coe_mul,
      Subgroup.coe_inv, Setup.rho_apply_coe]
    apply C.hV₁W
    have := inv_mem hc
    rwa [show ((z : G) * x * (z : G)⁻¹ * x⁻¹)⁻¹ = x * z * x⁻¹ * (z : G)⁻¹ by group] at this
  have hpos : ∀ X : Subgroup (Hat V H W), 0 < X.index := fun X =>
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hposU : 0 < Z.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [← Subgroup.index_ker]
  calc (A5Mod.commHom (C.act ⟨x, hBH hx⟩)).ker.index ≤ (Z.map q).index :=
        Nat.le_of_dvd (hpos _) (Subgroup.index_dvd_of_le hZf)
    _ ≤ Z.index := Nat.le_of_dvd hposU (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
    _ = (centralizerMod (fsuV1 T V) U B).relIndex U := rfl

theorem act_commHom_eq {B : Subgroup G} (hBH : B ≤ H)
    (hquad : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ u ∈ conjClosure V H,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V)
    {b₁ b₂ : G} (h₁ : b₁ ∈ B) (h₂ : b₂ ∈ B) (y : Hat V H W) :
    C.act ⟨b₂, hBH h₂⟩ (A5Mod.commHom (C.act ⟨b₁, hBH h₁⟩) y) =
      A5Mod.commHom (C.act ⟨b₁, hBH h₁⟩) y := by
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf (conjClosure V H)) y
  rw [C.commHom_act_mk, C.act_secMk, mk_eq_mk_iff]
  apply C.hV₁W
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
  exact hquad b₁ h₁ b₂ h₂ u u.2

theorem card_range_le_mul (x : ↥H) {D A : Subgroup G}
    (hxD : ∀ d ∈ D, (x : G) * d * (x : G)⁻¹ * d⁻¹ ∈ A) :
    Nat.card (A5Mod.commHom (C.act x)).range ≤ D.relIndex (conjClosure V H) * Nat.card A := by
  set U := conjClosure V H with hU
  set ρ := Setup.rho U H (le_normalizer_conjClosure V H) with hρ
  set κ : ↥U →* ↥U := A5Mod.commHom (ρ x) with hκ
  have hκc : ∀ u : ↥U, ((κ u : ↥U) : G) = x * u * (x : G)⁻¹ * (u : G)⁻¹ := by
    intro u
    rw [hκ, A5Mod.commHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, hρ, Setup.rho_apply_coe]
  have h1 : (A5Mod.commHom (C.act x)).range ≤ κ.range.map (InternalSec.secMk (W.subgroupOf U)) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf U) y
    exact ⟨κ u, ⟨u, rfl⟩, (C.commHom_act_mk x u).symm⟩
  have h2 := card_range_le_index_mul κ (D.subgroupOf U)
  have h3 : Nat.card ((D.subgroupOf U).map κ) ≤ Nat.card A := by
    have hmem : ∀ a ∈ (D.subgroupOf U).map κ, ((a : ↥U) : G) ∈ A := by
      rintro _ ⟨d, hd, rfl⟩
      rw [hκc]
      exact hxD d (Subgroup.mem_subgroupOf.mp hd)
    let ι : ↥((D.subgroupOf U).map κ) → ↥A := fun a => ⟨((a : ↥U) : G), hmem a a.2⟩
    refine Nat.card_le_card_of_injective ι fun a b hab => ?_
    have h4 : ((ι a : ↥A) : G) = ((ι b : ↥A) : G) := by rw [hab]
    exact Subtype.ext (Subtype.ext h4)
  calc Nat.card (A5Mod.commHom (C.act x)).range
      ≤ Nat.card (κ.range.map (InternalSec.secMk (W.subgroupOf U))) := Subgroup.card_le_of_le h1
    _ ≤ Nat.card κ.range := card_map_le' _ _
    _ ≤ (D.subgroupOf U).index * Nat.card ((D.subgroupOf U).map κ) := h2
    _ ≤ D.relIndex U * Nat.card A := Nat.mul_le_mul_left _ h3

end TopW

theorem card_le_index_of_inf_eq_bot {X : Type*} [CommGroup X] [Finite X] {A C : Subgroup X}
    (h : A ⊓ C = ⊥) : Nat.card A ≤ C.index := by
  have hinj : Function.Injective fun a : ↥A => (QuotientGroup.mk (a : X) : X ⧸ C) := by
    intro a b hab
    have h1 : (a : X)⁻¹ * b ∈ C := QuotientGroup.eq.mp hab
    have h2 : (a : X)⁻¹ * b ∈ A ⊓ C := ⟨A.mul_mem (A.inv_mem a.2) b.2, h1⟩
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2
  exact Nat.card_le_card_of_injective _ hinj

theorem mod50KIrr : Mod50KIrr := by
  intro G _ _ T L V H W K π C _ _ _ γ γ' g hh N J hJ
  by_contra hne
  push Not at hne
  obtain ⟨hJb, hJt⟩ := hne
  by_cases hall : ∀ h : ↥H, C.act h ∈ C.autK
  · rcases C.irr J (fun h y hy => hJ _ (hall h) y hy) with h | h
    · exact hJb h
    · exact hJt h
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have hpiT : π t ∉ alternatingGroup (Fin 7) := fun h => ht ((C.act_mem_autK_iff t).mpr h)
  have hodd : ∀ h : ↥H, C.act h ∉ C.autK → C.act h * (C.act t)⁻¹ ∈ C.autK := by
    intro h hh'
    have hpi : π h ∉ alternatingGroup (Fin 7) := fun h' => hh' ((C.act_mem_autK_iff h).mpr h')
    rw [← map_inv, ← map_mul, C.act_mem_autK_iff, mem_alternatingGroup, map_mul, map_inv, map_mul,
      map_inv]
    rw [mem_alternatingGroup] at hpi hpiT
    rcases Int.units_eq_one_or (sign (π h)) with h1 | h1
    · exact absurd h1 hpi
    rcases Int.units_eq_one_or (sign (π t)) with h2 | h2
    · exact absurd h2 hpiT
    rw [h1, h2]
    decide
  set τ := C.act t with hτ
  set J₁ : Subgroup (Hat V H W) := J.map τ.toMonoidHom with hJ₁
  have hmemJ₁ : ∀ y, y ∈ J₁ ↔ τ⁻¹ y ∈ J := by
    intro y
    rw [hJ₁, Subgroup.mem_map_equiv]
    rfl
  have hJ₁inv : ∀ l ∈ C.autK, ∀ y ∈ J₁, l y ∈ J₁ := by
    intro l hl y hy
    rw [hmemJ₁] at hy ⊢
    have hl' : τ⁻¹ * l * τ ∈ C.autK := by
      have := C.autK_normal τ⁻¹ (inv_mem ⟨t, rfl⟩) l hl
      simpa using this
    have := hJ _ hl' _ hy
    simpa [MulAut.mul_apply] using this
  have hτJ : ∀ y ∈ J, τ y ∈ J₁ := fun y hy => ⟨y, hy, rfl⟩
  have hpres : ∀ h : ↥H, C.act h ∈ C.autK →
      (∀ y ∈ J, C.act h y ∈ J) ∧ (∀ y ∈ J₁, C.act h y ∈ J₁) :=
    fun h hh' => ⟨fun y hy => hJ _ hh' y hy, fun y hy => hJ₁inv _ hh' y hy⟩
  have hswap : ∀ h : ↥H, C.act h ∉ C.autK →
      (∀ y ∈ J, C.act h y ∈ J₁) ∧ (∀ y ∈ J₁, C.act h y ∈ J) := by
    intro h hh'
    have hl' : C.act h * τ⁻¹ ∈ C.autK := hodd h hh'
    have e : C.act h = (C.act h * τ⁻¹) * τ := by rw [inv_mul_cancel_right]
    have hτ2 : τ * τ ∈ C.autK := by
      have := C.sq_mem τ ⟨t, rfl⟩
      rwa [pow_two] at this
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [e, MulAut.mul_apply]
      exact hJ₁inv _ hl' _ (hτJ y hy)
    · rw [hmemJ₁] at hy
      have e2 : C.act h y = (C.act h * τ⁻¹) ((τ * τ) (τ⁻¹ y)) := by
        simp [MulAut.mul_apply]
      rw [e2]
      exact hJ _ hl' _ (hJ _ hτ2 _ hy)
  have hperm : ∀ h : ↥H, ((∀ y ∈ J, C.act h y ∈ J) ∧ (∀ y ∈ J₁, C.act h y ∈ J₁)) ∨
      ((∀ y ∈ J, C.act h y ∈ J₁) ∧ (∀ y ∈ J₁, C.act h y ∈ J)) := by
    intro h
    by_cases hh' : C.act h ∈ C.autK
    · exact Or.inl (hpres h hh')
    · exact Or.inr (hswap h hh')
  have hinfI : ∀ h : ↥H, ∀ y ∈ J ⊓ J₁, C.act h y ∈ J ⊓ J₁ := by
    intro h y hy
    rcases hperm h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 y hy.1, h2 y hy.2⟩
    · exact ⟨h2 y hy.2, h1 y hy.1⟩
  have hsupI : ∀ h : ↥H, ∀ y ∈ J ⊔ J₁, C.act h y ∈ J ⊔ J₁ := by
    intro h y hy
    have hle : J ⊔ J₁ ≤ (J ⊔ J₁).comap (C.act h).toMonoidHom := by
      rcases hperm h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact sup_le (fun z hz => Subgroup.mem_sup_left (h1 z hz))
          (fun z hz => Subgroup.mem_sup_right (h2 z hz))
      · exact sup_le (fun z hz => Subgroup.mem_sup_right (h1 z hz))
          (fun z hz => Subgroup.mem_sup_left (h2 z hz))
    exact hle hy
  have hinf : J ⊓ J₁ = ⊥ := by
    rcases C.irr _ hinfI with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (by rw [← h]; exact inf_le_left)) hJt
  have hsup : J ⊔ J₁ = ⊤ := by
    rcases C.irr _ hsupI with h | h
    · exact absurd (eq_bot_iff.mpr (by rw [← h]; exact le_sup_left)) hJb
    · exact h
  have hJ₁b : J₁ ≠ ⊥ := by
    intro h
    apply hJb
    rw [eq_bot_iff]
    intro y hy
    have h1 : τ y ∈ J₁ := hτJ y hy
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (τ.injective (h1.trans (map_one τ).symm))
  have hmoves : ∀ Y : Subgroup (Hat V H W), Y ≠ ⊥ → ∃ l ∈ C.autK, ∃ y ∈ Y, l y * y⁻¹ ≠ 1 := by
    intro Y hY
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyF : y ∉ fixV C.autK := by
      rw [C.fixV_eq_bot, Subgroup.mem_bot]
      exact hy1'
    rw [mem_fixV] at hyF
    push Not at hyF
    obtain ⟨l, hl, hly⟩ := hyF
    exact ⟨l, hl, y, hy, fun h => hly (mul_inv_eq_one.mp h)⟩
  have hntJ := hmoves J hJb
  have hntTop : ∃ l ∈ C.autK, ∃ z ∈ (⊤ : Subgroup (Hat V H W)), l z * z⁻¹ ∉ J := by
    obtain ⟨l, hl, z, hz, hlz⟩ := hmoves J₁ hJ₁b
    refine ⟨l, hl, z, trivial, fun h => hlz ?_⟩
    have h2 : l z * z⁻¹ ∈ J₁ := J₁.mul_mem (hJ₁inv l hl z hz) (J₁.inv_mem hz)
    have h3 : l z * z⁻¹ ∈ J ⊓ J₁ := ⟨h, h2⟩
    rwa [hinf, Subgroup.mem_bot] at h3
  have hW2 : ∀ w : Hat V H W, w * w = 1 := C.sec_sq
  have h16 : ∀ e ∈ C.autK, e * e = 1 → e ≠ 1 → 16 ≤ Nat.card (A5Mod.commHom e).range :=
    fun e he he2 he1 => Alt7Mod.sixteen_le_card_range hW2 C.iota le_top hJ
      (fun _ _ _ _ => trivial) hntJ hntTop he he2 he1
  have hcardJ : 16 ≤ Nat.card J := by
    have hs : swap (0 : Fin 7) 1 * swap 2 3 ∈ alternatingGroup (Fin 7) :=
      mem_alternatingGroup.mpr (by decide)
    set e₀ : MulAut (Hat V H W) := ((C.iota.symm ⟨_, hs⟩ : ↥C.autK) : MulAut (Hat V H W))
      with he₀
    have he₀K : e₀ ∈ C.autK := (C.iota.symm ⟨_, hs⟩).2
    have hsq : swap (0 : Fin 7) 1 * swap 2 3 * (swap 0 1 * swap 2 3) = 1 := by decide
    have hsne : swap (0 : Fin 7) 1 * swap 2 3 ≠ 1 := by decide
    have hs2 : (⟨_, hs⟩ : alternatingGroup (Fin 7)) * ⟨_, hs⟩ = 1 := Subtype.ext hsq
    have he₀2 : e₀ * e₀ = 1 := by
      rw [he₀, ← Subgroup.coe_mul, ← map_mul, hs2, map_one]
      rfl
    have he₀1 : e₀ ≠ 1 := by
      intro h
      have h1 : C.iota.symm ⟨_, hs⟩ = 1 := Subtype.ext h
      have h2 := congrArg C.iota h1
      rw [MulEquiv.apply_symm_apply, map_one] at h2
      exact hsne (congrArg Subtype.val h2)
    have hee : ∀ y, e₀ (e₀ y) = y := fun y => by
      rw [← MulAut.mul_apply, he₀2, MulAut.one_apply]
    have h4 : 4 ≤ (⊥ : Subgroup (Hat V H W)).relIndex (J.map (A5Mod.commHom e₀)) :=
      Alt7Mod.four_le_relIndex_map hW2 C.iota
        (fun _ _ _ h => by rw [Subgroup.mem_bot.mp h, map_one]; exact one_mem _) hJ (by
          obtain ⟨l, hl, y, hy, hly⟩ := hntJ
          exact ⟨l, hl, y, hy, fun h => hly (Subgroup.mem_bot.mp h)⟩) he₀K he₀2 he₀1
    rw [Subgroup.relIndex_bot_left] at h4
    have hker := Subgroup.relIndex_ker (K := J) (A5Mod.commHom e₀)
    have hmul := Subgroup.relIndex_mul_card (A5Mod.commHom e₀).ker J
    have hle : J.map (A5Mod.commHom e₀) ≤ (A5Mod.commHom e₀).ker ⊓ J := by
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, J.mul_mem (hJ e₀ he₀K y hy) (J.inv_mem hy)⟩
      rw [MonoidHom.mem_ker]
      show A5Mod.commHom e₀ (A5Mod.commHom e₀ y) = 1
      rw [A5Mod.commHom_apply, A5Mod.commHom_apply, map_mul, map_inv, hee, mul_inv_rev, inv_inv]
      exact hW2 _
    have hc := Subgroup.card_le_of_le hle
    rw [hker] at hmul
    nlinarith
  obtain ⟨hcrit, heq⟩ := C.hF.F916_2_aux N.setup N.pos N.le
  obtain ⟨hUH, hUab, hUQ, hquad, hc⟩ := hcrit
  set Uγ := F8.Uγ V H (g : G) with hUγ
  have hE : Nat.card (C.autE Uγ) = (Uγ ⊓ pCoreOf 2 H).relIndex Uγ := C.card_autE hUH
  rw [← hE] at hc
  have hx2 : ∀ x (hx : x ∈ Uγ), C.act ⟨x, hUH hx⟩ * C.act ⟨x, hUH hx⟩ = 1 := by
    intro x hx
    rw [← map_mul]
    have h2 : x ^ 2 = 1 := hUab.2 x hx
    rw [show (⟨x, hUH hx⟩ : ↥H) * ⟨x, hUH hx⟩ = 1 from Subtype.ext (by rw [← pow_two]; exact h2),
      map_one]
  by_cases hUodd : ∃ b, ∃ hb : b ∈ Uγ, C.act ⟨b, hUH hb⟩ ∉ C.autK
  ·
    obtain ⟨b, hbU, hb⟩ := hUodd
    obtain ⟨hbJ, hbJ₁⟩ := hswap _ hb
    have hEven1 : ∀ b' (hb' : b' ∈ Uγ), C.act ⟨b', hUH hb'⟩ ∈ C.autK → C.act ⟨b', hUH hb'⟩ = 1 := by
      intro b' hb' hb'K
      obtain ⟨hp1, hp2⟩ := hpres _ hb'K
      have hfix : ∀ y, C.act ⟨b, hUH hbU⟩ (A5Mod.commHom (C.act ⟨b', hUH hb'⟩) y) =
          A5Mod.commHom (C.act ⟨b', hUH hb'⟩) y := fun y => C.act_commHom_eq hUH hquad hb' hbU y
      have hJk : J ≤ (A5Mod.commHom (C.act ⟨b', hUH hb'⟩)).ker := by
        intro y hy
        have hz : A5Mod.commHom (C.act ⟨b', hUH hb'⟩) y ∈ J := J.mul_mem (hp1 y hy) (J.inv_mem hy)
        have hz1 : A5Mod.commHom (C.act ⟨b', hUH hb'⟩) y ∈ J₁ := by
          rw [← hfix]
          exact hbJ _ hz
        have : A5Mod.commHom (C.act ⟨b', hUH hb'⟩) y ∈ J ⊓ J₁ := ⟨hz, hz1⟩
        rwa [hinf, Subgroup.mem_bot] at this
      have hJ₁k : J₁ ≤ (A5Mod.commHom (C.act ⟨b', hUH hb'⟩)).ker := by
        intro y hy
        have hz : A5Mod.commHom (C.act ⟨b', hUH hb'⟩) y ∈ J₁ :=
          J₁.mul_mem (hp2 y hy) (J₁.inv_mem hy)
        have hz1 : A5Mod.commHom (C.act ⟨b', hUH hb'⟩) y ∈ J := by
          rw [← hfix]
          exact hbJ₁ _ hz
        have : A5Mod.commHom (C.act ⟨b', hUH hb'⟩) y ∈ J ⊓ J₁ := ⟨hz1, hz⟩
        rwa [hinf, Subgroup.mem_bot] at this
      have htop : (⊤ : Subgroup (Hat V H W)) ≤ (A5Mod.commHom (C.act ⟨b', hUH hb'⟩)).ker :=
        hsup ▸ sup_le hJk hJ₁k
      refine MulEquiv.ext fun y => ?_
      have h1 := htop (Subgroup.mem_top y)
      rw [MonoidHom.mem_ker, A5Mod.commHom_apply, mul_inv_eq_one] at h1
      exact h1
    have hE2 : Nat.card (C.autE Uγ) ≤ 2 := by
      classical
      have hinj : Function.Injective fun e : ↥(C.autE Uγ) => decide ((e : MulAut _) ∈ C.autK) := by
        rintro ⟨_, ⟨⟨b₁, hb₁H⟩, hb₁, rfl⟩⟩ ⟨_, ⟨⟨b₂, hb₂H⟩, hb₂, rfl⟩⟩ h12
        have hb₁' : b₁ ∈ Uγ := Subgroup.mem_subgroupOf.mp hb₁
        have hb₂' : b₂ ∈ Uγ := Subgroup.mem_subgroupOf.mp hb₂
        apply Subtype.ext
        simp only at h12 ⊢
        by_cases h1 : C.act ⟨b₁, hb₁H⟩ ∈ C.autK
        · have h2 : C.act ⟨b₂, hb₂H⟩ ∈ C.autK := by
            by_contra h2
            simp [h1, h2] at h12
          rw [hEven1 b₁ hb₁' h1, hEven1 b₂ hb₂' h2]
        · have h2 : C.act ⟨b₂, hb₂H⟩ ∉ C.autK := by
            intro h2
            simp [h1, h2] at h12
          have hq : C.act ⟨b₁, hb₁H⟩ * (C.act ⟨b₂, hb₂H⟩)⁻¹ ∈ C.autK := by
            have := C.autK.mul_mem (hodd _ h1) (C.autK.inv_mem (hodd _ h2))
            simpa [mul_assoc] using this
          have hb12 : b₁ * b₂⁻¹ ∈ Uγ := Uγ.mul_mem hb₁' (Uγ.inv_mem hb₂')
          have e : C.act ⟨b₁ * b₂⁻¹, hUH hb12⟩ = C.act ⟨b₁, hb₁H⟩ * (C.act ⟨b₂, hb₂H⟩)⁻¹ := by
            rw [← map_inv, ← map_mul]
            rfl
          have h3 := hEven1 _ hb12 (e ▸ hq)
          rw [e, mul_inv_eq_one] at h3
          exact h3
      have := Nat.card_le_card_of_injective _ hinj
      simpa using this
    have hJker : J ⊓ (A5Mod.commHom (C.act ⟨b, hUH hbU⟩)).ker = ⊥ := by
      rw [eq_bot_iff]
      intro y hy'
      obtain ⟨hy, hyk⟩ := Subgroup.mem_inf.mp hy'
      rw [MonoidHom.mem_ker, A5Mod.commHom_apply, mul_inv_eq_one] at hyk
      have h1 : y ∈ J₁ := hyk ▸ hbJ y hy
      have : y ∈ J ⊓ J₁ := ⟨hy, h1⟩
      rwa [hinf] at this
    have h1 := card_le_index_of_inf_eq_bot hJker
    rw [Subgroup.index_ker] at h1
    have h2 := C.card_range_le_relIndex hUH hbU
    have h3 : Nat.card (C.autE Uγ) ^ 2 ≤ 4 := by nlinarith
    omega
  ·
    push Not at hUodd
    have hEK : C.autE Uγ ≤ C.autK := by
      rintro _ ⟨⟨b, hbH⟩, hb, rfl⟩
      exact hUodd b (Subgroup.mem_subgroupOf.mp hb)
    have hE4 : Nat.card (C.autE Uγ) ≤ 4 := by
      set P : Subgroup (alternatingGroup (Fin 7)) :=
        ((C.autE Uγ).subgroupOf C.autK).map C.iota.toMonoidHom with hP
      have hPc : Nat.card P = Nat.card (C.autE Uγ) := by
        rw [hP, Subgroup.card_map_of_injective (f := C.iota.toMonoidHom) C.iota.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv]
      rw [← hPc]
      refine Alt7.card_le_four ?_
      rintro _ ⟨⟨l, hl⟩, hlE, rfl⟩
      obtain ⟨⟨b, hbH⟩, hb, hbl⟩ := Subgroup.mem_subgroupOf.mp hlE
      have hbl' : C.act ⟨b, hbH⟩ = l := hbl
      rw [← map_mul]
      have h1 : (⟨l, hl⟩ : ↥C.autK) * ⟨l, hl⟩ = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        rw [← hbl']
        exact hx2 b (Subgroup.mem_subgroupOf.mp hb)
      rw [MulEquiv.coe_toMonoidHom, h1, map_one]
    obtain ⟨x, hxU, hxQ⟩ := Set.not_subset.mp hUQ
    have hxK := hUodd x hxU
    have hx1 : C.act ⟨x, hUH hxU⟩ ≠ 1 := fun h =>
      hxQ ((C.pi_eq_one_iff _).mp ((C.act_eq_one_iff _).mp h))
    have h16x := h16 _ hxK (hx2 x hxU) hx1
    have hlow := C.card_range_le_relIndex hUH hxU
    have hlow16 : 16 ≤
        (centralizerMod (fsuV1 T V) (conjClosure V H) Uγ).relIndex (conjClosure V H) :=
      h16x.trans hlow
    have hE4' : 4 ≤ Nat.card (C.autE Uγ) := by nlinarith
    have hEeq : Nat.card (C.autE Uγ) = 4 := le_antisymm hE4 hE4'
    have hc16 : (centralizerMod (fsuV1 T V) (conjClosure V H) Uγ).relIndex (conjClosure V H) =
        16 := by
      rw [hEeq] at hc
      norm_num at hc
      omega
    have hUp : IsPGroup 2 Uγ := isPGroup_of_isElemAbelian hUab
    have hUHp : IsPGroup 2 (conjClosure V H) := isPGroup_of_isElemAbelian C.hF.F911_3
    have hDγ := C.hF.Dγ_eq_inf_pCoreOf N.setup
    have hm1 : mIdx Uγ (F8.Dγ V (fsuV1 T V) H (g : G)) = 2 := by
      have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := F8.Dγ V (fsuV1 T V) H (g : G)) hUp
      rw [hDγ] at h1 ⊢
      rw [← hE, hEeq] at h1
      exact Nat.pow_right_injective le_rfl (h1.symm.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
    have hm2 : mIdx (conjClosure V H) (centralizerMod (fsuV1 T V) (conjClosure V H) Uγ) = 4 := by
      have h1 := HypF98.relIndex_eq_two_pow_mIdx
        (Y := centralizerMod (fsuV1 T V) (conjClosure V H) Uγ) hUHp
      rw [hc16] at h1
      exact Nat.pow_right_injective le_rfl (h1.symm.trans (by norm_num : (16 : ℕ) = 2 ^ 4))
    obtain ⟨hmDH, -, hcomm, hA₁, -, -⟩ := heq (by rw [hm1, hm2])
    have hDH4 : (F8.DH V (fsuV1 T V) H (g : G)).relIndex (conjClosure V H) = 4 := by
      have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := F8.DH V (fsuV1 T V) H (g : G)) hUHp
      rw [h1, ← hmDH, hm1]
      norm_num
    have h8 := C.card_range_le_mul ⟨x, hUH hxU⟩ (D := F8.DH V (fsuV1 T V) H (g : G))
      (A := F8.A₁ (fsuV1 T V) (g : G)) fun d hd =>
        hcomm (Subgroup.commutator_mem_commutator hxU hd)
    rw [hDH4, hA₁] at h8
    have := h16x.trans h8
    omega

theorem lemma14_7_50_mod_holds (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK)
    (h38 : Lemma14_7_38) (h48 : Lemma14_7_48) : Lemma14_7_50_Mod :=
  lemma14_7_50_mod_of_kIrr h1222 h1332 h1334 hA37 hA38 hA39 h38 h48 mod50KIrr

end CFSG.Quasithin.H13.L32A.C
