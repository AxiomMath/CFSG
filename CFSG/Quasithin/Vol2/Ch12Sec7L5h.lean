module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5f

public section

namespace CFSG.Quasithin.H13.S127.L5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

section Center

theorem map_center_eq_centerOf (K : Subgroup G) :
    (Subgroup.center ↥K).map K.subtype = centerOf K := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hk ⟨g, hg⟩)
  · rintro ⟨hxK, hxc⟩
    refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hxc g g.2

theorem card_center_eq (K : Subgroup G) :
    Nat.card ↥(Subgroup.center ↥K) = Nat.card ↥(centerOf K) := by
  rw [← map_center_eq_centerOf, Subgroup.card_map_of_injective K.subtype_injective]

theorem isPGroup_center {K : Subgroup G} (hZ : IsPGroup 2 ↥(centerOf K)) :
    IsPGroup 2 ↥(Subgroup.center ↥K) := by
  intro z
  have hz : ((z : ↥K) : G) ∈ centerOf K := by
    rw [← map_center_eq_centerOf]
    exact ⟨z, z.2, rfl⟩
  obtain ⟨n, hn⟩ := hZ ⟨_, hz⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hn
  simpa using this

theorem eq_one_of_mem_centerOf {K : Subgroup G} (h : Subgroup.center ↥K = ⊥) {x : G}
    (hx : x ∈ centerOf K) : x = 1 := by
  rw [← map_center_eq_centerOf, h, Subgroup.map_bot] at hx
  exact Subgroup.mem_bot.mp hx

theorem center_eq_bot_of_isSimpleGroup {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    [IsSimpleGroup X] : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨-, hs⟩ := hX
    have : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact false_of_nontrivial_of_subsingleton (X ⧸ Subgroup.center X)

end Center

section Orders

theorem dvd_card_of_isExt {X : Type} [Group X] {PN PQ : ∀ (V : Type) [Group V], Prop}
    (h : IsExt X PN PQ) {q : ℕ} (hq : ∀ (Y : Type) [Group Y], PQ Y → q ∣ Nat.card Y) :
    q ∣ Nat.card X := by
  obtain ⟨N, _, -, hY⟩ := h
  exact (hq _ hY).trans (Subgroup.card_quotient_dvd_card N)

theorem card_imageModCenter_dvd {K M₀ : Subgroup G} (hM0K : M₀ ≤ K) :
    Nat.card ↥(imageModCenter K M₀) ∣ Nat.card ↥M₀ := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM0K).toEquiv]
  exact Subgroup.card_map_dvd _ _

theorem seven_dvd_of_isPSL_three (Y : Type) [Group Y] (h : IsPSL 3 2 1 Y) : 7 ∣ Nat.card Y := by
  rw [SBc11.card_of_isPSL_three_two h]
  norm_num

theorem seven_dvd_of_isPSL_four (Y : Type) [Group Y] (h : IsPSL 4 2 1 Y) : 7 ∣ Nat.card Y := by
  rw [card_of_isPSL_two1522 4 h]
  decide

theorem seven_dvd_of_isPSL_five (Y : Type) [Group Y] (h : IsPSL 5 2 1 Y) : 7 ∣ Nat.card Y := by
  rw [card_of_isPSL_two1522 5 h]
  decide

theorem seven_dvd_of_isAlt_seven (Y : Type) [Group Y] (h : IsAlt 7 Y) : 7 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem seven_dvd_of_isPSU (Y : Type) [Group Y] (h : IsPSU 3 3 1 Y) : 7 ∣ Nat.card Y := by
  rw [SBc11.card_of_isPSU_three_three h]
  norm_num

theorem nine_dvd_of_isAlt_six (Y : Type) [Group Y] (h : IsAlt 6 Y) : 9 ∣ Nat.card Y := by
  rw [SBc11.card_of_isAlt_six h]
  norm_num

theorem nine_dvd_of_isHat (Y : Type) [Group Y] (h : IsHat Y ↥(alternatingGroup (Fin 6))) :
    9 ∣ Nat.card Y := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), h3,
    Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem seven_dvd_of_isSporadic_M24 (Y : Type) [Group Y]
    (h : IsSporadic .M24 Y) : 7 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change 7 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M24
  rw [CFSG.Sporadic.Mathieu.card_M24]
  norm_num

end Orders

variable [Finite G]

theorem card_le_of_isExt_image {K M₀ W : Subgroup G} (hM0K : M₀ ≤ K)
    (hZ : IsPGroup 2 ↥(centerOf K)) (hWM : W ≤ M₀)
    (hWO : W.subgroupOf M₀ ≤ CFSG.pCore 2 ↥M₀) (N : Subgroup ↥(imageModCenter K M₀))
    [N.Normal] (hN : IsPGroup 2 ↥N)
    (hcard : Nat.card (↥(imageModCenter K M₀) ⧸ N) = Nat.card (ModO2 M₀)) :
    Nat.card ↥W ≤ Nat.card ↥N * Nat.card ↥(W ⊓ centerOf K) := by
  classical
  let φ : ↥M₀ →* ↥(imageModCenter K M₀) :=
    ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hM0K)).codRestrict _
      (fun m => Subgroup.mem_map_of_mem _
        (show Subgroup.inclusion hM0K m ∈ M₀.subgroupOf K from m.2))
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨k, hk⟩, hkM, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨k, hkM⟩, rfl⟩
  have hφ1 : ∀ m : ↥M₀, φ m = 1 ↔ (m : G) ∈ centerOf K := by
    intro m
    rw [← map_center_eq_centerOf]
    constructor
    · intro hm
      have h2 : (QuotientGroup.mk' (Subgroup.center ↥K)) ⟨m, hM0K m.2⟩ = 1 :=
        congrArg Subtype.val hm
      exact ⟨_, (QuotientGroup.eq_one_iff _).mp h2, rfl⟩
    · rintro ⟨k, hk, hkm⟩
      apply Subtype.ext
      show (QuotientGroup.mk' (Subgroup.center ↥K)) ⟨m, hM0K m.2⟩ = 1
      have hk' : (⟨m, hM0K m.2⟩ : ↥K) = k := Subtype.ext hkm.symm
      rw [hk', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
  have hpow : ∀ m : ↥M₀, (m : G) ∈ centerOf K → ∃ b : ℕ, m ^ 2 ^ b = 1 := by
    intro m hm
    obtain ⟨b, hb⟩ := hZ ⟨m, hm⟩
    refine ⟨b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simpa using this
  set ψ : ↥M₀ →* ↥(imageModCenter K M₀) ⧸ N := (QuotientGroup.mk' N).comp φ with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective N).comp hφs
  have hψ1 : ∀ m : ↥M₀, m ∈ ψ.ker ↔ φ m ∈ N := by
    intro m
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hker2 : IsPGroup 2 ↥ψ.ker := by
    rintro ⟨m, hm⟩
    obtain ⟨a, ha⟩ := hN ⟨_, (hψ1 m).mp hm⟩
    have hφa : φ (m ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := hpow _ ((hφ1 _).mp hφa)
    refine ⟨a + b, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
    exact hb
  have hkerle : ψ.ker ≤ CFSG.pCore 2 ↥M₀ := le_sSup ⟨MonoidHom.normal_ker _, hker2⟩
  have hkereq : ψ.ker = CFSG.pCore 2 ↥M₀ := by
    refine Subgroup.eq_of_le_of_card_ge hkerle ?_
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥M₀)
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv, hcard] at h1
    have hpos : 0 < Nat.card (ModO2 M₀) := Nat.card_pos
    have h3 : Nat.card (ModO2 M₀) * Nat.card ↥ψ.ker =
        Nat.card (ModO2 M₀) * Nat.card ↥(CFSG.pCore 2 ↥M₀) := h1.symm.trans h2
    exact (Nat.eq_of_mul_eq_mul_left hpos h3).ge
  have hWN : ∀ w : ↥W, φ (Subgroup.inclusion hWM w) ∈ N := by
    intro w
    rw [← hψ1, hkereq]
    exact hWO (Subgroup.mem_subgroupOf.mpr w.2)
  set χ : ↥W →* ↥N := (φ.comp (Subgroup.inclusion hWM)).codRestrict N hWN with hχ
  have hW := Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv] at hW
  rw [hW]
  refine Nat.mul_le_mul (Subgroup.card_le_card_group _) ?_
  let ι : ↥χ.ker → ↥(W ⊓ centerOf K) := fun k => ⟨((k : ↥W) : G), (k : ↥W).2, by
    have hk : χ k = 1 := k.2
    have hk' : φ (Subgroup.inclusion hWM (k : ↥W)) = 1 := congrArg Subtype.val hk
    exact (hφ1 _).mp hk'⟩
  refine Nat.card_le_card_of_injective ι fun a b hab => ?_
  have hab' : ((a : ↥W) : G) = ((b : ↥W) : G) :=
    congrArg (fun x : ↥(W ⊓ centerOf K) => (x : G)) hab
  exact Subtype.ext (Subtype.ext hab')

namespace D127

variable {T L V : Subgroup G} {t : G} (d : D127 G T L V t)
include d

theorem subgroupOf_le_pCore : V.subgroupOf (Lt L t) ≤ CFSG.pCore 2 ↥(Lt L t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sSup ⟨?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff d.v_le_lt]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (d.lt_le_normalizer hk) h).mp hh
  · exact (IsPGroup.of_card d.card_V).of_equiv (Subgroup.subgroupOfEquivOfLe d.v_le_lt).symm

theorem card_Lt : Nat.card ↥(Lt L t) = Nat.card ↥(CFSG.pCore 2 ↥(Lt L t)) * 60 := by
  have h60 : Nat.card (↥(Lt L t) ⧸ CFSG.pCore 2 ↥(Lt L t)) = 60 := d.card_modO2
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(Lt L t)), h60, mul_comm]

theorem card_V_le : Nat.card ↥V ≤ Nat.card ↥(CFSG.pCore 2 ↥(Lt L t)) := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.v_le_lt).toEquiv]
  exact Subgroup.card_le_of_le d.subgroupOf_le_pCore

theorem not_dvd_card_Lt {q : ℕ} (hq : Nat.Coprime q 2) (h60 : ¬ q ∣ 60) :
    ¬ q ∣ Nat.card ↥(Lt L t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(Lt L t)))
  rw [d.card_Lt, ha]
  intro hd
  exact h60 ((Nat.Coprime.pow_right a hq).dvd_of_dvd_mul_left hd)

theorem not_seven_dvd : ¬ 7 ∣ Nat.card ↥(Lt L t) :=
  d.not_dvd_card_Lt (by norm_num) (by norm_num)

theorem not_nine_dvd : ¬ 9 ∣ Nat.card ↥(Lt L t) :=
  d.not_dvd_card_Lt (by norm_num) (by norm_num)

end D127

end CFSG.Quasithin.H13.S127.L5
