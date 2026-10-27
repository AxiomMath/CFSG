module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqPar
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqOrb
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Basic
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueHatA6
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.H13.Lem1227Eq

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped IsMulCommutative

section Move

variable {W : Type*} [CommGroup W]

theorem range_moveHom_le_ker (hsq : ∀ w : W, w ^ 2 = 1) (a : MulAut W) (ha2 : a * a = 1) :
    (End1222.moveHom a).range ≤ (End1222.moveHom a).ker := by
  rintro _ ⟨v, rfl⟩
  rw [MonoidHom.mem_ker, End1222.moveHom_apply, End1222.moveHom_apply]
  have h1 : a (a v) = v := by
    have := congrArg (fun φ : MulAut W => φ v) ha2
    simpa using this
  rw [map_mul, map_inv, h1, mul_inv_rev, inv_inv, ← pow_two, mul_pow, inv_pow, hsq v, hsq (a v)]
  simp

theorem mem_stabSub_range_moveHom (a ζ : MulAut W) (hcomm : a * ζ = ζ * a) :
    ζ ∈ stabSub (End1222.moveHom a).range := by
  have key : ∀ g : MulAut W, a * g = g * a →
      ∀ w ∈ (End1222.moveHom a).range, g w ∈ (End1222.moveHom a).range := by
    rintro g hg _ ⟨v, rfl⟩
    refine ⟨g v, ?_⟩
    have h1 : a (g v) = g (a v) := congrArg (fun φ : MulAut W => φ v) hg
    rw [End1222.moveHom_apply, End1222.moveHom_apply, map_mul, map_inv, h1]
  have hinv : a * ζ⁻¹ = ζ⁻¹ * a := by
    calc a * ζ⁻¹ = ζ⁻¹ * (ζ * a) * ζ⁻¹ := by group
      _ = ζ⁻¹ * (a * ζ) * ζ⁻¹ := by rw [hcomm]
      _ = ζ⁻¹ * a := by group
  intro u
  constructor
  · intro hu
    have := key ζ⁻¹ hinv _ hu
    simpa using this
  · intro hu
    exact key ζ hcomm u hu

theorem card_range_moveHom_eq_four [Finite W] (hsq : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 64)
    (a ζ : MulAut W) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (hcomm : a * ζ = ζ * a) (hfpf : ∀ w, ζ w = w → w = 1) :
    Nat.card (End1222.moveHom a).range = 4 := by
  set f := End1222.moveHom a with hf
  have hmul : Nat.card f.range * Nat.card f.ker = 64 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h
    rw [← hW]
    exact h.symm
  have hle : Nat.card f.range ≤ Nat.card f.ker :=
    Subgroup.card_le_of_le (range_moveHom_le_ker hsq a ha2)
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ v := by
    by_contra h
    push Not at h
    exact ha1 (MulEquiv.ext h)
  have hge : 2 ≤ Nat.card f.range := by
    have : Nontrivial f.range :=
      ⟨⟨⟨f v, v, rfl⟩, 1, fun h => hv (by
        have h1 : f v = 1 := congrArg Subtype.val h
        rw [hf, End1222.moveHom_apply, mul_inv_eq_one] at h1
        exact h1)⟩⟩
    exact Finite.one_lt_card
  have hstab := mem_stabSub_range_moveHom a ζ hcomm
  have hmod : Nat.card f.range % 3 = 1 := by
    refine card_mod_three_of_fpf (resHom f.range ⟨ζ, hstab⟩) ?_ ?_
    · rw [← map_pow]
      have : (⟨ζ, hstab⟩ : stabSub f.range) ^ 3 = 1 := Subtype.ext (by simpa using hζ3)
      rw [this, map_one]
    · intro w hw
      have h1 : ζ (w : W) = w := congrArg Subtype.val hw
      exact Subtype.ext (hfpf _ h1)
  have hdvd : Nat.card f.range ∣ 64 := ⟨_, hmul.symm⟩
  generalize Nat.card f.range = n at *
  generalize Nat.card f.ker = k at *
  have hn8 : n ≤ 8 := by nlinarith
  interval_cases n <;> first | rfl | (exfalso; omega)

end Move

section Comm

variable {G : Type} [Group G] {V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem conj_mem_centralizer {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) {o : G}
    (ho : o ∈ Subgroup.centralizer (V : Set G)) :
    g * o * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) v).1 hv
  have h := Subgroup.mem_centralizer_iff.1 ho _ hv'
  calc v * (g * o * g⁻¹) = g * ((g⁻¹ * v * g) * o) * g⁻¹ := by group
    _ = g * (o * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
    _ = g * o * g⁻¹ * v := by group

@[expose] noncomputable def commHom (c : G) (hc : c ∈ Subgroup.normalizer (V : Set G)) :
    ↥V →* ↥V :=
  End1222.moveHom (conjAct V ⟨c, hc⟩)

@[expose] noncomputable def Wc (c : G) (hc : c ∈ Subgroup.normalizer (V : Set G)) : Subgroup G :=
  (commHom c hc).range.map V.subtype

theorem mem_Wc {c : G} {hc : c ∈ Subgroup.normalizer (V : Set G)} {x : G} :
    x ∈ Wc c hc ↔ ∃ v : ↥V, c * v * c⁻¹ * (v : G)⁻¹ = x := by
  unfold Wc
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨commHom c hc v, ⟨v, rfl⟩, rfl⟩

theorem Wc_le (c : G) (hc : c ∈ Subgroup.normalizer (V : Set G)) : Wc c hc ≤ V :=
  Subgroup.map_subtype_le _

theorem card_Wc_eq_range (c : G) (hc : c ∈ Subgroup.normalizer (V : Set G)) :
    Nat.card (Wc c hc) = Nat.card (commHom c hc).range :=
  Nat.card_congr (Subgroup.equivMapOfInjective _ V.subtype V.subtype_injective).symm.toEquiv

theorem mem_Wc_conj {c : G} (hc : c ∈ Subgroup.normalizer (V : Set G)) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) {o : G}
    (ho : o ∈ Subgroup.centralizer (V : Set G)) (hgc : g * c * g⁻¹ = o * c) {x : G}
    (hx : x ∈ Wc c hc) : g * x * g⁻¹ ∈ Wc c hc := by
  obtain ⟨v, rfl⟩ := mem_Wc.1 hx
  have hv' : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hg v).1 v.2
  refine mem_Wc.2 ⟨⟨g * v * g⁻¹, hv'⟩, ?_⟩
  have hcv : c * (g * v * g⁻¹) * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hc _).1 hv'
  have h1 := Subgroup.mem_centralizer_iff.1 ho _ hcv
  have h2 : o * (c * (g * v * g⁻¹) * c⁻¹) * o⁻¹ = c * (g * v * g⁻¹) * c⁻¹ :=
    mul_inv_eq_iff_eq_mul.2 h1.symm
  show c * (g * v * g⁻¹) * c⁻¹ * (g * v * g⁻¹)⁻¹ = g * (c * v * c⁻¹ * (v : G)⁻¹) * g⁻¹
  calc c * (g * v * g⁻¹) * c⁻¹ * (g * v * g⁻¹)⁻¹
      = (o * (c * (g * v * g⁻¹) * c⁻¹) * o⁻¹) * (g * v * g⁻¹)⁻¹ := by rw [h2]
    _ = (o * c) * (g * v * g⁻¹) * (o * c)⁻¹ * (g * v * g⁻¹)⁻¹ := by group
    _ = (g * c * g⁻¹) * (g * v * g⁻¹) * (g * c * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ := by rw [hgc]
    _ = g * (c * v * c⁻¹ * (v : G)⁻¹) * g⁻¹ := by group

end Comm

section HatSec

variable {G : Type} [Group G] [Finite G] {K V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem card_mod_three_of_zinv {U : Subgroup G} {z : G} (hUz : ∀ u ∈ U, z * u * z⁻¹ ∈ U)
    (hUV : U ≤ V) (hz3 : z ^ 3 ∈ Subgroup.centralizer (V : Set G))
    (hfpf : ∀ v ∈ V, z * v * z⁻¹ = v → v = 1) : Nat.card U % 3 = 1 := by
  have hzN : z ∈ Subgroup.normalizer (U : Set G) := mem_normalizer_of_conj_mem hUz
  refine CFSG.Quasithin.H13.card_mod_three_of_fpf (U.normalizerMonoidHom ⟨z, hzN⟩) ?_ ?_
  · rw [← map_pow]
    refine MulEquiv.ext fun w => Subtype.ext ?_
    have h1 : (((⟨z, hzN⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 3 :
        ↥(Subgroup.normalizer (U : Set G))) : G) = z ^ 3 := rfl
    show (z ^ 3) * (w : G) * (z ^ 3)⁻¹ = (w : G)
    have := Subgroup.mem_centralizer_iff.1 hz3 (w : G) (hUV w.2)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  · intro w hw
    have h1 : z * (w : G) * z⁻¹ = w := congrArg Subtype.val hw
    exact Subtype.ext (hfpf _ (hUV w.2) h1)

structure HatSetting (K V : Subgroup G) [IsMulCommutative ↥V] (z c : G) : Prop where
  normalizes : K ≤ Subgroup.normalizer (V : Set G)
  sq : ∀ v ∈ V, v ^ 2 = 1
  irr : IsIrreducibleUnder K V
  card : Nat.card V = 2 ^ 6
  zK : z ∈ K
  cK : c ∈ K
  z_not : z ∉ Subgroup.centralizer (V : Set G)
  z3 : z ^ 3 ∈ Subgroup.centralizer (V : Set G)
  zcomm : ∀ k ∈ K, z * k * z⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V : Set G)
  c_not : c ∉ Subgroup.centralizer (V : Set G)
  c2 : c ^ 2 ∈ Subgroup.centralizer (V : Set G)

namespace HatSetting

variable {z c : G} (hs : HatSetting K V z c)

include hs

omit [Finite G] in
theorem hc : c ∈ Subgroup.normalizer (V : Set G) := hs.normalizes hs.cK

omit [Finite G] in
theorem hz : z ∈ Subgroup.normalizer (V : Set G) := hs.normalizes hs.zK

theorem fpf : ∀ v ∈ V, z * v * z⁻¹ = v → v = 1 := by
  set J : Subgroup G := V ⊓ Subgroup.centralizer ({z} : Set G) with hJ
  have hJK : ∀ k ∈ K, ∀ x ∈ J, k * x * k⁻¹ ∈ J := by
    intro k hk x hx
    have hxV : x ∈ V := (Subgroup.mem_inf.1 hx).1
    have hxz : z * x * z⁻¹ = x := by
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 z rfl
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have hx'V : k * x * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hs.normalizes hk) x).1 hxV
    refine Subgroup.mem_inf.2 ⟨hx'V, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    set o := y * k * y⁻¹ * k⁻¹ with ho
    have hoC : o ∈ Subgroup.centralizer (V : Set G) := hs.zcomm k hk
    have hyk : y * k * y⁻¹ = o * k := by rw [ho]; group
    have ho' : o * (k * x * k⁻¹) * o⁻¹ = k * x * k⁻¹ :=
      mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hoC _ hx'V).symm
    have h2 : y * (k * x * k⁻¹) * y⁻¹ = k * x * k⁻¹ := by
      calc y * (k * x * k⁻¹) * y⁻¹ = (y * k * y⁻¹) * (y * x * y⁻¹) * (y * k * y⁻¹)⁻¹ := by group
        _ = (o * k) * x * (o * k)⁻¹ := by rw [hyk, hxz]
        _ = o * (k * x * k⁻¹) * o⁻¹ := by group
        _ = k * x * k⁻¹ := ho'
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hKJ : K ≤ Subgroup.normalizer (J : Set G) := fun k hk =>
    mem_normalizer_of_conj_mem (hJK k hk)
  rcases hs.irr.2 J inf_le_left hKJ with h | h
  · intro v hv hvz
    have hvJ : v ∈ J := Subgroup.mem_inf.2 ⟨hv, by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [mul_inv_eq_iff_eq_mul] at hvz
      exact hvz⟩
    rw [h] at hvJ
    exact Subgroup.mem_bot.1 hvJ
  · exfalso
    apply hs.z_not
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvJ : v ∈ J := by rw [h]; exact hv
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hvJ).2 z rfl).symm

theorem card_Wc : Nat.card (Wc c hs.hc) = 4 := by
  rw [card_Wc_eq_range]
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (hs.sq w w.2)
  have hW : Nat.card ↥V = 64 := by rw [hs.card]; norm_num
  have hcon : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)),
      conjAct V ⟨g, hg⟩ = 1 ↔ g ∈ Subgroup.centralizer (V : Set G) := fun {g} hg =>
    A4.conjAct_eq_one_iff (g := ⟨g, hg⟩)
  have ha2 : conjAct V ⟨c, hs.hc⟩ * conjAct V ⟨c, hs.hc⟩ = 1 := by
    rw [← map_mul]
    refine A4.conjAct_eq_one_iff.2 ?_
    show c * c ∈ Subgroup.centralizer (V : Set G)
    rw [← pow_two]
    exact hs.c2
  have ha1 : conjAct V ⟨c, hs.hc⟩ ≠ 1 := fun h => hs.c_not ((hcon _).1 h)
  have hζ3 : conjAct V ⟨z, hs.hz⟩ ^ 3 = 1 := by
    rw [← map_pow]
    exact A4.conjAct_eq_one_iff.2 hs.z3
  have hcomm : conjAct V ⟨c, hs.hc⟩ * conjAct V ⟨z, hs.hz⟩ =
      conjAct V ⟨z, hs.hz⟩ * conjAct V ⟨c, hs.hc⟩ := by
    have hcz : c * z * c⁻¹ * z⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have := Subgroup.inv_mem _ (hs.zcomm c hs.cK)
      simpa [mul_assoc] using this
    have h1 : conjAct V (⟨c, hs.hc⟩ * ⟨z, hs.hz⟩ * ⟨c, hs.hc⟩⁻¹ * ⟨z, hs.hz⟩⁻¹) = 1 :=
      (hcon _).2 hcz
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  refine card_range_moveHom_eq_four hsq hW _ _ ha2 ha1 hζ3 hcomm ?_
  intro w hw
  have h1 : z * (w : G) * z⁻¹ = w := congrArg Subtype.val hw
  exact Subtype.ext (hs.fpf _ w.2 h1)

omit [Finite G] in
theorem Wc_conj_z : ∀ x ∈ Wc c hs.hc, z * x * z⁻¹ ∈ Wc c hs.hc := fun x hx =>
  mem_Wc_conj hs.hc hs.hz (o := z * c * z⁻¹ * c⁻¹) (hs.zcomm c hs.cK) (by group) hx

theorem not_le_normalizer : ¬ K ≤ Subgroup.normalizer (Wc c hs.hc : Set G) := by
  intro hK
  rcases hs.irr.2 (Wc c hs.hc) (Wc_le c hs.hc) hK with h | h
  · have := hs.card_Wc
    rw [h, Subgroup.card_bot] at this
    omega
  · have := hs.card_Wc
    rw [h, hs.card] at this
    omega

theorem relIndex_le : (K ⊓ Subgroup.normalizer (Wc c hs.hc : Set G)).relIndex K ≤ 21 := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let F : Set (Subgroup G) :=
    {U | U ≤ V ∧ Nat.card U = 4 ∧ ∀ u ∈ U, z * u * z⁻¹ ∈ U}
  have : Finite F := inferInstance
  have hW : Wc c hs.hc ∈ F := ⟨Wc_le c hs.hc, hs.card_Wc, hs.Wc_conj_z⟩
  have hF : ∀ k ∈ K, ∀ U ∈ F, cjSub k U ∈ F := by
    intro k hk U hU
    obtain ⟨hUV, hUc, hUz⟩ := hU
    have hkV := hs.normalizes hk
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [mem_cjSub] at hx
      have := (Subgroup.mem_normalizer_iff.1 hkV _).1 (hUV hx)
      simpa [mul_assoc] using this
    · rw [← hUc]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom)
        (MulAut.conj k).injective
    · intro y hy
      rw [mem_cjSub] at hy ⊢
      have hu := hUz _ hy
      set o' := k⁻¹ * (z * k * z⁻¹ * k⁻¹) * k with ho'
      have ho'C : o' ∈ Subgroup.centralizer (V : Set G) := by
        have := conj_mem_centralizer (V := V) (g := k⁻¹) (Subgroup.inv_mem _ hkV)
          (hs.zcomm k hk)
        simpa [ho', mul_assoc] using this
      have hyV : z * (k⁻¹ * y * k) * z⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 hs.hz _).1 (hUV hy)
      have h1 := Subgroup.mem_centralizer_iff.1 ho'C _ hyV
      have h2 : o' * (z * (k⁻¹ * y * k) * z⁻¹) * o'⁻¹ = z * (k⁻¹ * y * k) * z⁻¹ :=
        mul_inv_eq_iff_eq_mul.2 h1.symm
      have h3 : k⁻¹ * (z * y * z⁻¹) * k = o' * (z * (k⁻¹ * y * k) * z⁻¹) * o'⁻¹ := by
        rw [ho']
        group
      rw [h3, h2]
      exact hu
  have hdisj : ∀ U ∈ F, ∀ U' ∈ F, U ≠ U' → U ⊓ U' = ⊥ := by
    intro U hU U' hU' hne
    obtain ⟨hUV, hUc, hUz⟩ := hU
    obtain ⟨hU'V, hU'c, hU'z⟩ := hU'
    have hD : Nat.card ↥(U ⊓ U') % 3 = 1 :=
      card_mod_three_of_zinv (fun u hu => ⟨hUz u hu.1, hU'z u hu.2⟩) (inf_le_left.trans hUV)
        hs.z3 hs.fpf
    have hdvd : Nat.card ↥(U ⊓ U') ∣ 4 :=
      hUc ▸ Subgroup.card_dvd_of_le (inf_le_left : U ⊓ U' ≤ U)
    generalize hn : Nat.card ↥(U ⊓ U') = n at hD hdvd
    have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · exact absurd hD (by norm_num)
    · exact Subgroup.eq_bot_of_card_eq _ hn
    · exact absurd hD (by norm_num)
    · exact absurd hD (by norm_num)
    · exfalso
      apply hne
      have h1 : U ⊓ U' = U :=
        Subgroup.eq_of_le_of_card_ge (H := U ⊓ U') (K := U) inf_le_left (by omega)
      have h2 : U ⊓ U' = U' :=
        Subgroup.eq_of_le_of_card_ge (H := U ⊓ U') (K := U') inf_le_right (by omega)
      rw [← h1, h2]
  have hcard := card_family_le (⊥ : Subgroup G) V bot_le F 4
    (fun U hU => ⟨bot_le, hU.1⟩) (fun U hU => hU.2.1) hdisj
  rw [Subgroup.card_bot, hs.card] at hcard
  have h21 := relIndex_inf_normalizer_le K (Wc c hs.hc) F hW hF
  omega

end HatSetting

end HatSec

section Bridge

variable {G : Type} [Group G] [Finite G] {T K H M₀ V : Subgroup G}

theorem mem_pCoreOf_of_kerIn (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hker : KerChar M₀ H K) (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3)
    (hT2 : IsPGroup 2 ↥T) {n : G} (hnT : n ∈ T) (hnK : n ∈ K) (hn : n ∈ kerIn M₀ H) :
    n ∈ pCoreOf 2 K := by
  have hcen := (mem_kerIn_iff_central hKH hHK hker ⟨n, hnK⟩).1 hn
  obtain ⟨k, hk⟩ := hT2 ⟨n, hnT⟩
  have h1 : (QuotientGroup.mk (⟨n, hnK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 2 ^ k = 1 := by
    have : ((⟨n, hnT⟩ : ↥T) ^ 2 ^ k : ↥T) = 1 := hk
    have h2 : n ^ 2 ^ k = 1 := congrArg Subtype.val this
    rw [← QuotientGroup.mk_pow]
    have h3 : (⟨n, hnK⟩ : ↥K) ^ 2 ^ k = 1 := Subtype.ext (by simpa using h2)
    rw [h3]
    rfl
  have h3 : (QuotientGroup.mk (⟨n, hnK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
      (x := ⟨_, hcen⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hord : orderOf (QuotientGroup.mk (⟨n, hnK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
    have d1 := orderOf_dvd_of_pow_eq_one h1
    have d2 := orderOf_dvd_of_pow_eq_one h3
    have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := Nat.dvd_gcd d1 d2
    rw [hcop] at this
    exact Nat.dvd_one.1 this
  have hx1 := orderOf_eq_one_iff.1 hord
  exact (mem_pCore_iff_coe ⟨n, hnK⟩).1 ((QuotientGroup.eq_one_iff _).1 hx1)

theorem conj_eq_of_unique_central_involution {Γ : Type*} [Group Γ] {S : Subgroup Γ} {d : Γ}
    (hdS : d ∈ Subgroup.normalizer (S : Set Γ)) {c : Γ} (hc : c ∈ S) (hc1 : c ≠ 1)
    (hc2 : c ^ 2 = 1) (huniq : ∀ c' ∈ S, c' ≠ 1 → c' ^ 2 = 1 →
      (∀ s ∈ S, c' * s = s * c') → c' = c) (hcc : ∀ s ∈ S, c * s = s * c) :
    d * c * d⁻¹ = c := by
  refine huniq _ ((Subgroup.mem_normalizer_iff.1 hdS c).1 hc) ?_ ?_ ?_
  · intro h
    apply hc1
    have : c = d⁻¹ * (d * c * d⁻¹) * d := by group
    rw [this, h]
    group
  · have : (d * c * d⁻¹) ^ 2 = d * c ^ 2 * d⁻¹ := by
      simp only [pow_two]
      group
    rw [this, hc2]
    group
  · intro s hs
    have hs' : d⁻¹ * s * d ∈ S := by
      simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hdS) s).1 hs
    have h1 := hcc _ hs'
    calc d * c * d⁻¹ * s = d * (c * (d⁻¹ * s * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * s * d) * c) * d⁻¹ := by rw [h1]
      _ = s * (d * c * d⁻¹) := by group

theorem not_isDiagramNontrivial_of_hat [IsMulCommutative ↥V] (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hsq : ∀ v ∈ V, v ^ 2 = 1) (hirr : IsIrreducibleUnder K V)
    (hcent : K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 K) (hV : Nat.card V = 2 ^ 6)
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3)
    (hiso : Nonempty (↥(E2.star M₀ H K) ≃* Alt6)) :
    ¬ E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)) := by
  have hO : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) := hcent ▸ inf_le_right
  have hOker : pCoreOf 2 K ≤ kerIn M₀ H :=
    (pCoreOf_le_pCoreOf_of_normal hKH hHK).trans hmin.pCoreOf_le_kerIn
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  have hTH : T ≤ H := hmin.isSylow.1
  have hZne : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨zb, hzbc⟩, hzb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZne
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zb
  have hz1 : (QuotientGroup.mk z : ↥K ⧸ CFSG.pCore 2 ↥K) ≠ 1 := fun h => hzb1 (Subtype.ext h)
  have hzcomm : ∀ k ∈ K, (z : G) * k * (z : G)⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro k hk
    have h1 := Subgroup.mem_center_iff.1 hzbc (QuotientGroup.mk ⟨k, hk⟩)
    have h2 := (mk_comm_iff (CFSG.pCore 2 ↥K) z ⟨k, hk⟩).1 h1.symm
    exact hO ((mem_pCore_iff_coe (z * ⟨k, hk⟩ * z⁻¹ * ⟨k, hk⟩⁻¹)).1 h2)
  have hz3 : (z : G) ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    have h3 : (QuotientGroup.mk z : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
        (x := ⟨_, hzbc⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
    exact hO ((mem_pCore_iff_coe (z ^ 3)).1 h3)
  have hz_not : (z : G) ∉ Subgroup.centralizer (V : Set G) := by
    intro hzC
    apply hz1
    rw [QuotientGroup.eq_one_iff, mem_pCore_iff_coe, ← hcent]
    exact Subgroup.mem_inf.2 ⟨z.2, hzC⟩
  obtain ⟨-, hSyl⟩ := isSylowTwoOf_star hKH hHK hmin
  obtain ⟨e⟩ := hiso
  have hS' : IsSylowTwoOf ((E2.star M₀ H (T ⊓ K)).subgroupOf (E2.star M₀ H K)) ⊤ := by
    rw [isSylowTwoOf_top_iff']
    exact ⟨hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm, hSyl.2.2⟩
  have hA6 := A6Syl.of_sylow e hS'
  obtain ⟨cs, hcsS, hcs1, hcs2, hcsc, hcsu⟩ := hA6.central
  have hcsT : (cs : E2.StarQuot M₀ H) ∈ E2.star M₀ H (T ⊓ K) := Subgroup.mem_subgroupOf.1 hcsS
  have hcs1' : (cs : E2.StarQuot M₀ H) ≠ 1 := fun h => hcs1 (Subtype.ext h)
  have hcs2' : (cs : E2.StarQuot M₀ H) ^ 2 = 1 := by simpa using congrArg Subtype.val hcs2
  have hcsc' : ∀ s ∈ E2.star M₀ H (T ⊓ K), (cs : E2.StarQuot M₀ H) * s = s * cs := fun s hs =>
    congrArg Subtype.val (hcsc ⟨s, hSyl.1 hs⟩ (Subgroup.mem_subgroupOf.2 hs))
  have hcsu' : ∀ c' ∈ E2.star M₀ H (T ⊓ K), c' ≠ 1 → c' ^ 2 = 1 →
      (∀ s ∈ E2.star M₀ H (T ⊓ K), c' * s = s * c') → c' = cs := by
    intro c' hc' hne hsq' hcomm
    exact congrArg Subtype.val (hcsu ⟨c', hSyl.1 hc'⟩ (Subgroup.mem_subgroupOf.2 hc')
      (fun h => hne (congrArg Subtype.val h)) (Subtype.ext (by simpa using hsq'))
      (fun s hs => Subtype.ext (hcomm s (Subgroup.mem_subgroupOf.1 hs))))
  obtain ⟨h, hh, hhcs⟩ := mem_star_iff.1 hcsT
  have hcT : (h : G) ∈ T := (Subgroup.mem_inf.1 hh).1
  have hcK : (h : G) ∈ K := (Subgroup.mem_inf.1 hh).2
  have hcnot : (h : G) ∉ Subgroup.centralizer (V : Set G) := by
    intro hcC
    apply hcs1'
    rw [← hhcs]
    have hcO : (h : G) ∈ pCoreOf 2 K := by
      rw [← hcent]
      exact Subgroup.mem_inf.2 ⟨hcK, hcC⟩
    show (QuotientGroup.mk h : E2.StarQuot M₀ H) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hOker hcO
  have hc2 : (h : G) ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
    have hker2 : (h : G) ^ 2 ∈ kerIn M₀ H := by
      have h1 : (QuotientGroup.mk (h ^ 2) : E2.StarQuot M₀ H) = 1 := by
        rw [QuotientGroup.mk_pow]
        change (starMk M₀ H h) ^ 2 = 1
        rw [hhcs]
        exact hcs2'
      have := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    exact hO (mem_pCoreOf_of_kerIn hKH hHK hker hZ hT2 (T.pow_mem hcT 2) (K.pow_mem hcK 2) hker2)
  have hs : HatSetting K V (z : G) (h : G) :=
    ⟨hKV, hsq, hirr, hV, z.2, hcK, hz_not, hz3, hzcomm, hcnot, hc2⟩
  have hTW : T ≤ Subgroup.normalizer (Wc (h : G) hs.hc : Set G) := by
    intro t ht
    have htH : t ∈ H := hTH ht
    have hdS : starMk M₀ H ⟨t, htH⟩ ∈
        Subgroup.normalizer ((E2.star M₀ H (T ⊓ K) : Subgroup (E2.StarQuot M₀ H)) :
          Set (E2.StarQuot M₀ H)) :=
      star_le_normalizer_star (le_normalizer_inf_self hTK)
        (mem_star_iff.2 ⟨⟨t, htH⟩, ht, rfl⟩)
    have hconj : starMk M₀ H ⟨t, htH⟩ * cs * (starMk M₀ H ⟨t, htH⟩)⁻¹ = cs :=
      conj_eq_of_unique_central_involution hdS hcsT hcs1' hcs2' hcsu' hcsc'
    have hoT : t * (h : G) * t⁻¹ * (h : G)⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht)) (T.inv_mem hcT)
    have hoK : t * (h : G) * t⁻¹ * (h : G)⁻¹ ∈ K := by
      have h1 : t * (h : G) * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hTK ht) _).1 hcK
      exact K.mul_mem h1 (K.inv_mem hcK)
    have hoker : t * (h : G) * t⁻¹ * (h : G)⁻¹ ∈ kerIn M₀ H := by
      have h1 : (QuotientGroup.mk (⟨t, htH⟩ * h * ⟨t, htH⟩⁻¹ * h⁻¹ : ↥H) :
          E2.StarQuot M₀ H) = 1 := by
        change starMk M₀ H ⟨t, htH⟩ * starMk M₀ H h * (starMk M₀ H ⟨t, htH⟩)⁻¹ *
          (starMk M₀ H h)⁻¹ = 1
        rw [hhcs, hconj, mul_inv_cancel]
      have := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have ho := hO (mem_pCoreOf_of_kerIn hKH hHK hker hZ hT2 hoT hoK hoker)
    refine mem_normalizer_of_conj_mem (fun x hx => ?_)
    exact mem_Wc_conj hs.hc (hTV ht) ho (by group) hx
  have hJW : K ⊓ kerIn M₀ H ≤ Subgroup.normalizer (Wc (h : G) hs.hc : Set G) := by
    rintro n ⟨hnK, hnker⟩
    have hcen := (mem_kerIn_iff_central hKH hHK hker ⟨n, hnK⟩).1 hnker
    have h1 := Subgroup.mem_center_iff.1 hcen (QuotientGroup.mk ⟨(h : G), hcK⟩)
    have h2 := (mk_comm_iff (CFSG.pCore 2 ↥K) ⟨n, hnK⟩ ⟨(h : G), hcK⟩).1 h1.symm
    have ho : n * (h : G) * n⁻¹ * (h : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      hO ((mem_pCore_iff_coe _).1 h2)
    refine mem_normalizer_of_conj_mem (fun x hx => ?_)
    exact mem_Wc_conj hs.hc (hKV hnK) ho (by group) hx
  exact not_isDiagramNontrivial_of_stable_subgroup hKH hHK hmin hTK ⟨e⟩ hTW hJW
    hs.not_le_normalizer (hs.relIndex_le.trans (by norm_num))

end Bridge

end CFSG.Quasithin.H13.Lem1227Eq
