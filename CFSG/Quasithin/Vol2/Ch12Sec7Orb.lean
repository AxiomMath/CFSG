module

public import CFSG.Quasithin.Vol2.Ch12Sec7Disp
public import CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch12Sec7Thm7
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitHatA6
public import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6Six
public import CFSG.Quasithin.Background.F420Orders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_quot_of_hatA6Quot {L V : Subgroup G} (h : HatA6Quot L V) :
    Nat.card (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) = 1080 := by
  obtain ⟨_, -, h3, ⟨e⟩⟩ := h
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L)),
    Nat.card_congr e.toEquiv, hA6, h3]

theorem dvd_card_quot_pCore {L V : Subgroup G} (h : HatA6Quot L V) {X : Type} [Group X]
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* X) : 135 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1080 := dvd_card_of_hatA6Quot h
  have hcard := (CFSG.pCore 2 ↥L).card_eq_card_quotient_mul_card_subgroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  rw [Nat.card_congr e.toEquiv, hk] at hcard
  have h135 : 135 ∣ Nat.card X * 2 ^ k := hcard ▸ (dvd_trans (by norm_num) h1080)
  exact (Nat.Coprime.pow_right _ (by norm_num)).dvd_of_dvd_mul_right h135

theorem card_alternating_ne {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    Nat.card ↥(alternatingGroup (Fin n)) ≠ 1080 := by
  interval_cases n <;> rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide

theorem card_eq_of_1222 (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    IsMulCommutative ↥V ∧ Nat.card V = 2 ^ 6 ∧ T ≤ Subgroup.normalizer (V : Set G) := by
  have hy := h.hyp
  obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
    hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, ⟨hcomm, hmod⟩⟩ := hall V hy.irrPlus
  refine ⟨hcomm, ?_, hTV⟩
  have hQ := card_quot_of_hatA6Quot h.hatA6
  have hsl : ∀ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) →
      ¬ 135 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    intro n hn
    rcases hn with rfl | rfl | rfl <;> rw [Matrix.card_SL_field, ZMod.card] <;> decide
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨m, hm5, hm8, ⟨φ, hφ, hker⟩, -⟩ | ⟨-, φ, hφ, hker⟩ | ⟨hU, -⟩ | ⟨-, -, -, -, h64, -⟩
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl n hn)
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl 3 (Or.inl rfl))
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl 5 (Or.inr (Or.inr rfl)))
  · exfalso
    apply card_alternating_ne hm5 hm8
    rw [← hQ, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
  · exfalso
    apply card_alternating_ne (n := 7) (by norm_num) (by norm_num)
    rw [← hQ, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
  · exfalso
    rcases hU with ⟨-, hU⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have h135 := dvd_card_quot_pCore h.hatA6 (MulEquiv.refl _)
      rw [F420.card_of_u33 hU] at h135
      exact absurd h135 (by decide)
    all_goals exact absurd h0 (by norm_num)
  · exact h64

omit [Finite G] in
theorem autOn_hat {L V : Subgroup G} (h : HatA6Quot L V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Group.IsPerfect ↥(autOn L V) ∧ Nat.card (Subgroup.center ↥(autOn L V)) = 3 ∧
      Nonempty (↥(autOn L V) ⧸ Subgroup.center ↥(autOn L V) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨_, hq, h3, ⟨e6⟩⟩ := h
  let eQ : ↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L ≃* ↥(autOn L V) :=
    (QuotientGroup.quotientMulEquivOfEq (ker_autOnSurj hLV).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (autOnSurj_surjective hLV))
  have : Group.IsPerfect (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) := hq.1
  refine ⟨Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr eQ).toEquiv]
    exact h3
  · exact ⟨(QuotientGroup.congr _ _ eQ.symm (Subgroup.map_center_eq eQ.symm)).trans e6⟩

omit [Finite G] in
theorem mem_orbitIn_autOn_iff {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (v w : ↥V) :
    w ∈ Orbit.orbitIn (autOn L V) v ↔ ∃ l ∈ L, l * (v : G) * l⁻¹ = w := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).1 ha
    exact ⟨l, l.2, (A4.actionOn_apply_coe hLV l v).symm⟩
  · rintro ⟨l, hl, hlw⟩
    refine ⟨A4.actionOn V L hLV ⟨l, hl⟩, (A4.mem_autOn_iff hLV).2 ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [A4.actionOn_apply_coe]
    exact hlw

theorem card_orbitIn_autOn {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    Nat.card (Orbit.orbitIn (autOn L V) v) =
      (Subgroup.centralizer ({(v : G)} : Set G)).relIndex L := by
  classical
  have himg : Subtype.val '' Orbit.orbitIn (autOn L V) v =
      Sporadic.Schreier.conjClass L (v : G) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨l, hl, hlw⟩ := (mem_orbitIn_autOn_iff hLV v w).1 hw
      exact ⟨l, hl, hlw.symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c * v * c⁻¹, (Subgroup.mem_normalizer_iff.1 (hLV hc) v).1 v.2⟩,
        (mem_orbitIn_autOn_iff hLV v _).2 ⟨c, hc, rfl⟩, rfl⟩
  have h1 : Nat.card (Orbit.orbitIn (autOn L V) v) =
      (Sporadic.Schreier.conjClass L (v : G)).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_coe_set_eq]
  have h2 := Sporadic.Schreier.ncard_conjClass_mul_card L (v : G)
  have h3 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({(v : G)} : Set G)) (K := L)
  rw [Sporadic.Schreier.centralizerIn, inf_comm] at h2
  rw [h1]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h3.symm)

theorem orbits_of_1222 (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    ∃ z ∈ V, ∃ t ∈ V, (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 ∧
      (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 ∧
      ∀ v ∈ V, v ≠ 1 → (∃ l ∈ L, l * v * l⁻¹ = z) ∨ (∃ l ∈ L, l * v * l⁻¹ = t) := by
  classical
  obtain ⟨hcomm, hV64, -⟩ := card_eq_of_1222 h1222 h
  have := hcomm
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  obtain ⟨hperf, hZ3, he⟩ := autOn_hat h.hatA6 hLV
  have hsq : ∀ v : ↥V, v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using sq_eq_one_of_mem h.hyp v.2)
  obtain ⟨hlen, hsep⟩ := orbitHatA6Six_of Orbit.orbitTripleA6Six hatA6SixModel ↥V hsq hV64
    (autOn L V) hperf hZ3 he
  set H := autOn L V with hHdef
  have h63 : ({1}ᶜ : Set ↥V).ncard = 63 := by
    rw [Set.compl_eq_univ_sdiff, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _),
      Set.ncard_univ, hV64]
    norm_num
  have hnot : ∀ w : ↥V, w ≠ 1 → ¬ ∀ u : ↥V, u ≠ 1 → u ∈ Orbit.orbitIn H w := by
    intro w hw hall
    have hsub : ({1}ᶜ : Set ↥V) ⊆ Orbit.orbitIn H w := fun u hu => hall u hu
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h63, ← Nat.card_coe_set_eq] at hle
    have hmem := hlen w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    omega
  have : Nontrivial ↥V := Finite.one_lt_card_iff_nontrivial.1 (by rw [hV64]; norm_num)
  obtain ⟨w₀, hw₀⟩ := exists_ne (1 : ↥V)
  have hex : ∀ ℓ ∈ [18, 45], ∃ w : ↥V, w ≠ 1 ∧ Nat.card (Orbit.orbitIn H w) = ℓ := by
    intro ℓ hℓ
    by_contra hno
    have hno' : ∀ u : ↥V, u ≠ 1 → Nat.card (Orbit.orbitIn H u) ≠ ℓ := fun u hu hc =>
      hno ⟨u, hu, hc⟩
    have hℓ' : ∀ u : ↥V, u ≠ 1 → Nat.card (Orbit.orbitIn H u) = 63 - ℓ := by
      intro u hu
      have hu' := hlen u hu
      have hne := hno' u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu' hℓ
      omega
    apply hnot w₀ hw₀
    intro u hu
    obtain ⟨a, ha, hau⟩ := hsep w₀ u hw₀ hu ((hℓ' w₀ hw₀).trans (hℓ' u hu).symm)
    exact ⟨a, ha, hau⟩
  obtain ⟨z, hz1, hz45⟩ := hex 45 (by simp)
  obtain ⟨t, ht1, ht18⟩ := hex 18 (by simp)
  refine ⟨z, z.2, t, t.2, ?_, ?_, fun v hv hv1 => ?_⟩
  · rw [← card_orbitIn_autOn hLV z]
    exact hz45
  · rw [← card_orbitIn_autOn hLV t]
    exact ht18
  · have hv1' : (⟨v, hv⟩ : ↥V) ≠ 1 := fun h1 => hv1 (congrArg Subtype.val h1)
    have hmem := hlen ⟨v, hv⟩ hv1'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h18 | h45
    · right
      obtain ⟨a, ha, hat⟩ := hsep _ t hv1' ht1 (h18.trans ht18.symm)
      exact (mem_orbitIn_autOn_iff hLV ⟨v, hv⟩ t).1 ⟨a, ha, hat⟩
    · left
      obtain ⟨a, ha, haz⟩ := hsep _ z hv1' hz1 (h45.trans hz45.symm)
      exact (mem_orbitIn_autOn_iff hLV ⟨v, hv⟩ z).1 ⟨a, ha, haz⟩

theorem exists_fixed_of_isPGroup {T V : Subgroup G} (hT : IsPGroup 2 T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV : 2 ∣ Nat.card V) :
    ∃ z ∈ V, z ≠ 1 ∧ T ≤ Subgroup.centralizer ({z} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥T ↥V := MulAction.compHom ↥V (Subgroup.inclusion hTV)
  have hsmul : ∀ (s : ↥T) (v : ↥V), ((s • v : ↥V) : G) = s * v * (s : G)⁻¹ := fun _ _ => rfl
  have hmod := hT.card_modEq_card_fixedPoints (α := ↥V)
  have h2 : 2 ∣ Nat.card (MulAction.fixedPoints ↥T ↥V) :=
    (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hV)))
  have h1 : (1 : ↥V) ∈ MulAction.fixedPoints ↥T ↥V := fun s => Subtype.ext (by simp [hsmul])
  have hlt : 1 < Nat.card (MulAction.fixedPoints ↥T ↥V) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥T ↥V) :=
      Nat.card_pos_iff.2 ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    omega
  have := Finite.one_lt_card_iff_nontrivial.1 hlt
  obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (⟨1, h1⟩ : MulAction.fixedPoints ↥T ↥V)
  refine ⟨w, w.2, fun h1' => hw1 (Subtype.ext (Subtype.ext h1')), fun s hs => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg Subtype.val (hw ⟨s, hs⟩)
  rw [hsmul] at h
  calc s * (w : G) = s * w * s⁻¹ * s := by group
    _ = w * s := by rw [h]

theorem lemma12_7_4_part1_of (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    ∃ z ∈ V1 T L V, z ≠ 1 ∧ T ≤ Subgroup.centralizer ({z} : Set G) ∧ ∃ t ∈ V, t ≠ 1 ∧
      (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 ∧
      (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 ∧
      ∀ v ∈ V, v ≠ 1 → (∃ l ∈ L, l * v * l⁻¹ = z) ∨ (∃ l ∈ L, l * v * l⁻¹ = t) := by
  obtain ⟨z₀, -, t₀, ht₀, h45, h18, horb⟩ := orbits_of_1222 h1222 h
  obtain ⟨-, hV64, hTV⟩ := card_eq_of_1222 h1222 h
  obtain ⟨z, hzV, hz1, hTz⟩ := exists_fixed_of_isPGroup h.hyp.sylow.1 hTV
    (by rw [hV64]; norm_num)
  have hzV₁ : z ∈ V1 T L V := by
    refine Subgroup.mem_inf.2 ⟨hzV, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hTz (Subgroup.mem_inf.1 hx).1)
  have hodd := not_two_dvd_relIndex h.hyp hTz
  obtain ⟨l, hl, hlz⟩ : ∃ l ∈ L, l * z * l⁻¹ = z₀ := by
    rcases horb z hzV hz1 with hz | ⟨l, hl, hlz⟩
    · exact hz
    · rw [← hlz, relIndex_centralizer_conj hl] at h18
      exact absurd ⟨9, h18⟩ hodd
  have hz45 : (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 := by
    rw [← relIndex_centralizer_conj hl, hlz, h45]
  refine ⟨z, hzV₁, hz1, hTz, t₀, ht₀, ne_one_of_relIndex h18 (by decide), hz45, h18,
    fun v hv hv1 => ?_⟩
  rcases horb v hv hv1 with ⟨m, hm, hmv⟩ | ht
  · refine Or.inl ⟨l⁻¹ * m, L.mul_mem (L.inv_mem hl) hm, ?_⟩
    rw [← hlz] at hmv
    calc l⁻¹ * m * v * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * v * m⁻¹) * l := by group
      _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [hmv]
      _ = z := by group
  · exact Or.inr ht

end S127

theorem lemma12_7_4_one_of_1222 (h1222 : Stmt12_2_2) : Lemma12_7_4_one :=
  fun _ _ _ _ _ _ h => S127.orbits_of_1222 h1222 h

end CFSG.Quasithin.H13
