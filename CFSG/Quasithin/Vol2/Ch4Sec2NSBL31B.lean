module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Typ
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312KG

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}

private theorem conj_mem_centralizer_nsb31b {V : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hz : z ∈ Subgroup.centralizer (V : Set G)) :
    g * z * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro v hv
  have hw : g⁻¹ * v * g⁻¹⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
  obtain ⟨w, hwdef⟩ : ∃ w, w = g⁻¹ * v * g⁻¹⁻¹ := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have hwz : w * z = z * w := hz w hw
  have hv' : v = g * w * g⁻¹ := by rw [hwdef]; group
  rw [hv']
  calc g * w * g⁻¹ * (g * z * g⁻¹) = g * (w * z) * g⁻¹ := by group
    _ = g * (z * w) * g⁻¹ := by rw [hwz]
    _ = g * z * g⁻¹ * (g * w * g⁻¹) := by group

private theorem sup_le_normalizer_V_nsb31b (c : Conf4212 G T M L I H K) :
    L ⊔ T ≤ Subgroup.normalizer (vV T L : Set G) := by
  have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
    rw [← c.omega_eq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  have hSN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := _root_.sup_le Subgroup.le_normalizer hTN
  intro g hg
  exact mem_normalizer_commutator (hRN hg) (hSN hg)

private theorem pow_mem_L_nsb31b (c : Conf4212 G T M L I H K) {x : G} (hx : x ∈ L ⊔ T) :
    ∃ e : ℕ, x ^ 2 ^ e ∈ L := by
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  rw [sup_comm] at hx
  obtain ⟨t, ht, l, hl, rfl⟩ := (mem_sup_of_le_normalizer hTN).mp hx
  have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTN ht) l).mp hl
  obtain ⟨k, hk⟩ := c.hyp421.sylow.1 ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨x', hx', hpow⟩ := A4.exists_pow_mul_eq hl' (hTN ht) (2 ^ k)
  refine ⟨k, ?_⟩
  have e : t * l = t * l * t⁻¹ * t := by group
  rw [e, hpow, htk, mul_one]
  exact hx'

private theorem mem_pCore_iff_nsb31b {L : Subgroup G} (z : ↥L) :
    (z : G) ∈ pCoreOf 2 L ↔ z ∈ CFSG.pCore 2 ↥L := by
  constructor
  · rintro ⟨w, hw, hwz⟩
    have : w = z := Subtype.ext hwz
    exact this ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

private theorem inf_le_pCoreOf_centralizer_nsb31b (hd : NoSumBigData G T M L Mm I H K m k) {x : G}
    (hxL : x ∈ L) (hxN : x ∈ Subgroup.centralizer (vV T L : Set G)) : x ∈ pCoreOf 2 L := by
  have c := hd.2.2.1
  have hpsl : IsPSL m 2 1 (ModO2 L) := by
    obtain ⟨e⟩ := c.nonempty_modO2_equiv
    exact T4213.isPSL_of_mulEquiv e hd.2.2.2.2.2.2.1
  have hs : IsSimpleGroup (ModO2 L) := InspA312.isSimpleGroup_of_isPSL hpsl
  have hN0 : pCoreOf 2 L ≤ Subgroup.centralizer (vV T L : Set G) :=
    c.pCoreOf_le_centralizer_V c.pCoreOf_L_le
  let Y : Subgroup ↥L := Subgroup.comap L.subtype (Subgroup.centralizer (vV T L : Set G))
  have hYmem : ∀ y : ↥L, y ∈ Y ↔ (y : G) ∈ Subgroup.centralizer (vV T L : Set G) :=
    fun y => Iff.rfl
  have hYn : Y.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hYmem] at hn ⊢
    have h1 := conj_mem_centralizer_nsb31b (c.L_le_normalizer_V g.2) hn
    simpa using h1
  have hYb : (Y.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    Subgroup.Normal.map hYn _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (Y.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with
    hbot | htop
  · have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨x, hxL⟩ ∈
        Y.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map_of_mem _ ((hYmem _).mpr hxN)
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact (mem_pCore_iff_nsb31b _).mpr hmem
  · exfalso
    have hLN : ∀ l ∈ L, l ∈ Subgroup.centralizer (vV T L : Set G) := by
      intro l hl
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨l, hl⟩ ∈
          Y.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyl⟩ := Subgroup.mem_map.mp hmem
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyl
      have h2 : ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := (mem_pCore_iff_nsb31b _).mpr hyl
      have h3 : ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ Subgroup.centralizer (vV T L : Set G) := hN0 h2
      have e : l = (y : G) * ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
      rw [e]
      exact Subgroup.mul_mem _ ((hYmem y).mp hy) h3
    have hLH : perfectCore (L ⊓ H) ≤ L := (perfectCore_le _).trans inf_le_left
    have hcc : conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) :=
      conjClosure_eq_self c.LH_normal
    have hVc : ⁅vV T L, perfectCore (L ⊓ H)⁆ = vV T L := by
      have h := c.hypC28.V_comm
      rw [hcc] at h
      exact h
    have hbot' : ⁅vV T L, perfectCore (L ⊓ H)⁆ = ⊥ := by
      apply le_bot_iff.mp
      refine Subgroup.commutator_le.mpr fun v hv l hl => ?_
      have hlN := hLN l (hLH hl)
      have hvl : v * l = l * v := Subgroup.mem_centralizer_iff.mp hlN v hv
      rw [Subgroup.mem_bot, commutatorElement_def, hvl]
      group
    exact c.hypC28.V_ne (hVc.symm.trans hbot')

theorem inf_centralizer_vV_eq (hd : NoSumBigData G T M L Mm I H K m k) :
    L ⊓ Subgroup.centralizer (vV T L : Set G) = pCoreOf 2 L := by
  refine le_antisymm (fun x hx => inf_le_pCoreOf_centralizer_nsb31b hd hx.1 hx.2) ?_
  exact le_inf (pCoreOf_le 2 L) (hd.2.2.1.pCoreOf_le_centralizer_V hd.2.2.1.pCoreOf_L_le)

private theorem hcen_nsb31b (hd : NoSumBigData G T M L Mm I H K m k) {x : G} (hxL : x ∈ L)
    (hx : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (vV T L : Set G)) :
    x ∈ pCoreOf 2 L := by
  have c := hd.2.2.1
  have hpsl : IsPSL m 2 1 (ModO2 L) := by
    obtain ⟨e⟩ := c.nonempty_modO2_equiv
    exact T4213.isPSL_of_mulEquiv e hd.2.2.2.2.2.2.1
  have hs : IsSimpleGroup (ModO2 L) := InspA312.isSimpleGroup_of_isPSL hpsl
  have hnc : ∃ a b : ModO2 L, a * b ≠ b * a := InspA312.exists_noncomm_of_isPSL hpsl
  have hcen0 : Subgroup.center (ModO2 L) = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (ModO2 L)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have ha : a ∈ Subgroup.center (ModO2 L) := by
        rw [h]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hxc : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩ : ModO2 L) ∈
      Subgroup.center (ModO2 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    apply (mem_pCore_iff_nsb31b _).mp
    have hN : ((y : G) * x)⁻¹ * (x * (y : G)) ∈ Subgroup.centralizer (vV T L : Set G) := by
      have hy1 : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ Subgroup.centralizer (vV T L : Set G) :=
        hx y y.2
      have hyN : (y : G)⁻¹ ∈ Subgroup.normalizer (vV T L : Set G) :=
        c.L_le_normalizer_V (L.inv_mem y.2)
      have hxN : x⁻¹ ∈ Subgroup.normalizer (vV T L : Set G) :=
        c.L_le_normalizer_V (L.inv_mem hxL)
      have z2 := conj_mem_centralizer_nsb31b hyN hy1
      have z3 := conj_mem_centralizer_nsb31b hxN z2
      have e : ((y : G) * x)⁻¹ * (x * (y : G)) =
          x⁻¹ * ((y : G)⁻¹ * (x * (y : G) * x⁻¹ * (y : G)⁻¹) * (y : G)⁻¹⁻¹) * x⁻¹⁻¹ := by
        group
      rw [e]
      exact z3
    have hLm : ((y : G) * x)⁻¹ * (x * (y : G)) ∈ L :=
      L.mul_mem (L.inv_mem (L.mul_mem y.2 hxL)) (L.mul_mem hxL y.2)
    have hmain := inf_le_pCoreOf_centralizer_nsb31b hd hLm hN
    simpa using hmain
  rw [hcen0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxc
  exact (mem_pCore_iff_nsb31b _).mpr hxc

private theorem mem_pCoreOf_sup_of_commutator_nsb31b {S L V : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hLS : L ≤ S)
    (hcen : ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
      x ∈ pCoreOf 2 L)
    (hpow : ∀ x ∈ S, ∃ e : ℕ, x ^ 2 ^ e ∈ L) :
    ∀ x ∈ S, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
      x ∈ pCoreOf 2 S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Subgroup G :=
    { carrier := {x | x ∈ S ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G)}
      mul_mem' := by
        rintro x y ⟨hxS, hxC⟩ ⟨hyS, hyC⟩
        refine ⟨S.mul_mem hxS hyS, fun l hl => ?_⟩
        have e : x * y * l * (x * y)⁻¹ * l⁻¹ =
            x * (y * l * y⁻¹ * l⁻¹) * x⁻¹ * (x * l * x⁻¹ * l⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (conj_mem_centralizer_nsb31b (hSV hxS) (hyC l hl)) (hxC l hl)
      one_mem' := ⟨S.one_mem, fun l _ => by simp⟩
      inv_mem' := by
        rintro x ⟨hxS, hxC⟩
        refine ⟨S.inv_mem hxS, fun l hl => ?_⟩
        have hl' : x * l⁻¹ * x⁻¹ * l⁻¹⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          hxC l⁻¹ (L.inv_mem hl)
        have hl'' : x * l⁻¹ * x⁻¹ * l ∈ Subgroup.centralizer (V : Set G) := by
          simpa using hl'
        have h1 : l * (x * l⁻¹ * x⁻¹ * l) * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          conj_mem_centralizer_nsb31b (hSV (hLS hl)) hl''
        have h2 : x⁻¹ * (l * (x * l⁻¹ * x⁻¹ * l) * l⁻¹) * x⁻¹⁻¹ ∈
            Subgroup.centralizer (V : Set G) :=
          conj_mem_centralizer_nsb31b (hSV (S.inv_mem hxS)) h1
        have e : x⁻¹ * l * x⁻¹⁻¹ * l⁻¹ = x⁻¹ * (l * (x * l⁻¹ * x⁻¹ * l) * l⁻¹) * x⁻¹⁻¹ := by
          group
        rw [e]
        exact h2 }
  have hDmem : ∀ x : G, x ∈ D ↔
      x ∈ S ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    fun x => Iff.rfl
  have hDS : D ≤ S := fun x hx => ((hDmem x).mp hx).1
  have hconj : ∀ y ∈ S, ∀ x ∈ D, y * x * y⁻¹ ∈ D := by
    intro y hy x hx
    obtain ⟨hxS, hxC⟩ := (hDmem x).mp hx
    rw [hDmem]
    refine ⟨S.mul_mem (S.mul_mem hy hxS) (S.inv_mem hy), fun l hl => ?_⟩
    have hl' : y⁻¹ * l * y⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hSN (S.inv_mem hy)) l).mp hl
    have h1 := conj_mem_centralizer_nsb31b (hSV hy) (hxC _ hl')
    have e : y * x * y⁻¹ * l * (y * x * y⁻¹)⁻¹ * l⁻¹ =
        y * (x * (y⁻¹ * l * y⁻¹⁻¹) * x⁻¹ * (y⁻¹ * l * y⁻¹⁻¹)⁻¹) * y⁻¹ := by
      group
    rw [e]
    exact h1
  have hSD : S ≤ Subgroup.normalizer (D : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj y hy x hx, fun hx => ?_⟩
    have h2 := hconj y⁻¹ (S.inv_mem hy) _ hx
    have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
    rwa [e] at h2
  have hDp : IsPGroup 2 D := by
    intro x
    obtain ⟨e, he⟩ := hpow (x : G) (hDS x.2)
    have hyD : (x : G) ^ 2 ^ e ∈ D := D.pow_mem x.2 _
    obtain ⟨f, hf⟩ := pCoreOf_isPGroup 2 L ⟨(x : G) ^ 2 ^ e, hcen _ he ((hDmem _).mp hyD).2⟩
    refine ⟨e + f, Subtype.ext ?_⟩
    have hf' : ((x : G) ^ 2 ^ e) ^ 2 ^ f = 1 := by
      have := congrArg Subtype.val hf
      simpa using this
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul]
    exact hf'
  have hDsub : D ≤ pCoreOf 2 S := le_pCoreOf_of_le_normalizer 2 hDS hSD hDp
  intro x hxS hxC
  exact hDsub ((hDmem x).mpr ⟨hxS, hxC⟩)

theorem T_le_L_rPlus (hd : NoSumBigData G T M L Mm I H K m k)
    (hI1 : ∀ t ∈ T, ∃ p ∈ L, ∀ l ∈ L,
      (p⁻¹ * t) * l * (p⁻¹ * t)⁻¹ * l⁻¹ ∈ Subgroup.centralizer (vV T L : Set G)) :
    ∀ t ∈ T, ∃ l ∈ L, ∃ c ∈ pCoreOf 2 (L ⊔ T), t = l * c := by
  have c := hd.2.2.1
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  have hSN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    _root_.sup_le Subgroup.le_normalizer hTN
  have hD := mem_pCoreOf_sup_of_commutator_nsb31b hSN (sup_le_normalizer_V_nsb31b c) le_sup_left
    (fun _ hx hcomm => hcen_nsb31b hd hx hcomm) (fun _ hx => pow_mem_L_nsb31b c hx)
  intro t ht
  obtain ⟨p, hp, hpt⟩ := hI1 t ht
  have hcS : p⁻¹ * t ∈ L ⊔ T :=
    (L ⊔ T).mul_mem ((L ⊔ T).inv_mem (Subgroup.mem_sup_left hp)) (Subgroup.mem_sup_right ht)
  exact ⟨p, hp, p⁻¹ * t, hD (p⁻¹ * t) hcS hpt, by group⟩

end CFSG.Quasithin.H13.Ch4.NSB
