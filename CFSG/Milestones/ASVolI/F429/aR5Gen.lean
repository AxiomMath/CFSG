module

public import CFSG.Milestones.ASVolI.F429.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin
open CFSG.LieType.BorelTits (pCoreOf_le pCoreOf_isPGroup le_pCoreOf_of_le_normalizer
  normalizer_le_normalizer_pCoreOf le_normalizer_pCoreOf)

section Generic

variable {E : Type} [Group E]

theorem burnsideF429a_oPPrime_le (P : Subgroup E) : oPPrime 2 P ≤ P :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem burnsideF429a_le_normalizer_oPPrime {P T : Subgroup E}
    (hT : T ≤ Subgroup.normalizer (P : Set E)) :
    T ≤ Subgroup.normalizer ((oPPrime 2 P : Subgroup E) : Set E) := by
  have key : ∀ s : E, s ∈ Subgroup.normalizer (P : Set E) →
      ∀ x ∈ oPPrime 2 P, s * x * s⁻¹ ∈ oPPrime 2 P := by
    intro s hs x hx
    have hmap : (oPPrime 2 P).map (MulAut.conj s).toMonoidHom ≤ oPPrime 2 P := by
      unfold oPPrime
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨y, ⟨hyP, k, hk⟩, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hs y).1 hyP, k, ?_⟩
      rw [← hk]
      exact orderOf_injective (MulAut.conj s).toMonoidHom (MulEquiv.injective _) y
    exact hmap ⟨x, hx, rfl⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key t (hT ht) x
  · intro hx
    have := key t⁻¹ (Subgroup.inv_mem _ (hT ht)) _ hx
    simpa [mul_assoc] using this

theorem burnsideF429a_relIndex_sup [Finite E] {L T : Subgroup E}
    (hTL : T ≤ Subgroup.normalizer (L : Set E)) :
    T.relIndex (L ⊔ T) = (L ⊓ T).relIndex L := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hTL
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTL
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient T L hTL
  have h1 : L.relIndex T = L.relIndex (T ⊔ L) := by
    unfold Subgroup.relIndex Subgroup.index
    exact Nat.card_congr e.toEquiv
  have hSp : 0 < Nat.card ↥(L ⊓ T) := Nat.card_pos
  have hc1 := Subgroup.relIndex_mul_card L (T ⊔ L)
  have hc2 := Subgroup.relIndex_mul_card L T
  have hc3 := Subgroup.relIndex_mul_card T (T ⊔ L)
  have hc4 := Subgroup.relIndex_mul_card (L ⊓ T) L
  rw [inf_eq_left.2 le_sup_right] at hc1
  rw [inf_eq_left.2 le_sup_left] at hc3
  rw [inf_eq_left.2 inf_le_left] at hc4
  rw [sup_comm]
  have hpos : 0 < L.relIndex T := by
    rcases Nat.eq_zero_or_pos (L.relIndex T) with h | h
    · have : Nat.card T = 0 := by rw [← hc2, h, zero_mul]
      exact absurd this Nat.card_pos.ne'
    · exact h
  have key : T.relIndex (T ⊔ L) * (L.relIndex T * Nat.card ↥(L ⊓ T)) =
      (L ⊓ T).relIndex L * (L.relIndex T * Nat.card ↥(L ⊓ T)) := by
    calc T.relIndex (T ⊔ L) * (L.relIndex T * Nat.card ↥(L ⊓ T))
        = T.relIndex (T ⊔ L) * Nat.card T := by rw [hc2]
      _ = Nat.card ↥(T ⊔ L) := hc3
      _ = L.relIndex (T ⊔ L) * Nat.card L := hc1.symm
      _ = L.relIndex T * ((L ⊓ T).relIndex L * Nat.card ↥(L ⊓ T)) := by rw [h1, hc4]
      _ = (L ⊓ T).relIndex L * (L.relIndex T * Nat.card ↥(L ⊓ T)) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos hSp) key

theorem burnsideF429a_exists_mul_eq_of_mem_sup {N H : Subgroup E}
    (hH : H ≤ Subgroup.normalizer (N : Set E)) {x : E} (hx : x ∈ N ⊔ H) :
    ∃ n ∈ N, ∃ y ∈ H, n * y = x := by
  let X : Subgroup E :=
    { carrier := {g | ∃ n ∈ N, ∃ y ∈ H, n * y = g}
      one_mem' := ⟨1, N.one_mem, 1, H.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, y₁, hy₁, rfl⟩ ⟨n₂, hn₂, y₂, hy₂, rfl⟩
        refine ⟨n₁ * (y₁ * n₂ * y₁⁻¹), N.mul_mem hn₁
          ((Subgroup.mem_normalizer_iff.mp (hH hy₁) n₂).mp hn₂), y₁ * y₂, H.mul_mem hy₁ hy₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨n, hn, y, hy, rfl⟩
        refine ⟨y⁻¹ * n⁻¹ * y⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem hy)) n⁻¹).mp
          (N.inv_mem hn), y⁻¹, H.inv_mem hy, ?_⟩
        group }
  exact (sup_le (fun n hn => ⟨n, hn, 1, H.one_mem, mul_one n⟩)
    (fun y hy => ⟨1, N.one_mem, y, hy, one_mul y⟩) : N ⊔ H ≤ X) hx

theorem burnsideF429a_mul_pow_mem {N : Subgroup E} {t : E}
    (ht : t ∈ Subgroup.normalizer (N : Set E)) {n : E} (hn : n ∈ N) (k : ℕ) :
    ∃ n' ∈ N, (n * t) ^ k = n' * t ^ k := by
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨n', hn', e⟩ := ih
    have htk : t ^ k ∈ Subgroup.normalizer (N : Set E) := Subgroup.pow_mem _ ht k
    refine ⟨n' * (t ^ k * n * (t ^ k)⁻¹), N.mul_mem hn'
      ((Subgroup.mem_normalizer_iff.mp htk n).mp hn), ?_⟩
    rw [pow_succ, e, pow_succ]
    group

theorem burnsideF429a_mem_pCoreOf_sup [Finite E] {L T Q : Subgroup E}
    (hTL : T ≤ Subgroup.normalizer (L : Set E)) (hTQ : T ≤ Subgroup.normalizer (Q : Set E))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set E)) (hQ : IsPGroup 2 Q) (hT : IsPGroup 2 T)
    (hZ : ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Q) → x ∈ Q)
    {y : E} (hy : y ∈ T) (hyc : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Q) :
    y ∈ pCoreOf 2 (L ⊔ T) := by
  have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set E) := sup_le Subgroup.le_normalizer hTL
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set E) := sup_le hLQ hTQ
  have hconjL : ∀ v ∈ L ⊔ T, ∀ l ∈ L, v⁻¹ * l * v ∈ L := by
    intro v hv l hl
    have := (Subgroup.mem_normalizer_iff.mp (hLT ((L ⊔ T).inv_mem hv)) l).mp hl
    simpa using this
  let C : Subgroup E :=
    { carrier := {w | w ∈ L ⊔ T ∧ ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ Q}
      one_mem' := ⟨(L ⊔ T).one_mem, fun l _ => by simp [Q.one_mem]⟩
      mul_mem' := by
        rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
        refine ⟨(L ⊔ T).mul_mem ha hb, fun l hl => ?_⟩
        have e : a * b * l * (a * b)⁻¹ * l⁻¹ =
            a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ * (a * l * a⁻¹ * l⁻¹) := by group
        rw [e]
        exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLTQ ha) _).mp (hbc l hl)) (hac l hl)
      inv_mem' := by
        rintro a ⟨ha, hac⟩
        refine ⟨(L ⊔ T).inv_mem ha, fun l hl => ?_⟩
        have h1 := hac _ (hconjL a ha l hl)
        have e : a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ = (a * (a⁻¹ * l * a) * a⁻¹ * (a⁻¹ * l * a)⁻¹)⁻¹ := by
          group
        rw [e]
        exact Q.inv_mem h1 }
  have hconj : ∀ v ∈ L ⊔ T, ∀ w ∈ C, v * w * v⁻¹ ∈ C := by
    rintro v hv w ⟨hw, hwc⟩
    refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hv hw) ((L ⊔ T).inv_mem hv), fun l hl => ?_⟩
    have e : v * w * v⁻¹ * l * (v * w * v⁻¹)⁻¹ * l⁻¹ =
        v * (w * (v⁻¹ * l * v) * w⁻¹ * (v⁻¹ * l * v)⁻¹) * v⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLTQ hv) _).mp (hwc _ (hconjL v hv l hl))
  have hCn : L ⊔ T ≤ Subgroup.normalizer (C : Set E) := fun v hv =>
    Subgroup.mem_normalizer_iff.mpr fun w => ⟨hconj v hv w, fun h => by
      have := hconj v⁻¹ ((L ⊔ T).inv_mem hv) _ h
      simpa [mul_assoc] using this⟩
  have hC2 : IsPGroup 2 C := by
    rintro ⟨w, hw, hwc⟩
    obtain ⟨n, hn, t, ht, rfl⟩ := burnsideF429a_exists_mul_eq_of_mem_sup hTL hw
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨n', hn', e⟩ := burnsideF429a_mul_pow_mem (hTL ht) hn (2 ^ a)
    rw [hta, mul_one] at e
    have hmemC : (n * t) ^ 2 ^ a ∈ C := C.pow_mem ⟨hw, hwc⟩ _
    have hQ' : (n * t) ^ 2 ^ a ∈ Q := hZ _ (e ▸ hn') hmemC.2
    obtain ⟨b, hb⟩ := hQ ⟨_, hQ'⟩
    have hb' : ((n * t) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
    exact hb'
  have hCle : C ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (fun w hw => hw.1) hCn hC2
  exact hCle ⟨Subgroup.mem_sup_right hy, hyc⟩

theorem burnsideF429a_exists_two_elt_not_mem [Finite E] {Gp H T : Subgroup E} [Gp.Normal]
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ x ∈ H, e = n * x) (hT : ChF.IsSylowOf 2 T H)
    (hev : ¬ Odd Gp.index) : ∃ t ∈ T, t ∉ Gp ∧ t * t ∈ Gp := by
  have hTG : ¬ T ≤ Gp := by
    intro hle
    apply hev
    have htop : Gp ⊔ H = ⊤ := by
      rw [eq_top_iff]
      intro e _
      obtain ⟨n, hn, x, hx, rfl⟩ := hsplit e
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hx)
    have h1 : Gp.index = (Gp ⊓ H).relIndex H := by
      rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_sup_left, htop,
        Subgroup.relIndex_top_right]
    have hTB : T ≤ Gp ⊓ H := le_inf hle hT.1
    have h2 : T.relIndex (Gp ⊓ H) * (Gp ⊓ H).relIndex H = T.relIndex H :=
      Subgroup.relIndex_mul_relIndex T (Gp ⊓ H) H hTB inf_le_right
    have h3 : ¬ 2 ∣ (Gp ⊓ H).relIndex H := fun hd => hT.2.2 (h2 ▸ Dvd.dvd.mul_left hd _)
    rw [h1, Nat.odd_iff]
    omega
  obtain ⟨t, htT, htG⟩ := Set.not_subset.mp hTG
  obtain ⟨k, hk⟩ := hT.2.1 ⟨t, htT⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hex : ∃ j, t ^ 2 ^ j ∈ Gp := ⟨k, hk' ▸ Gp.one_mem⟩
  classical
  have hjG : t ^ 2 ^ Nat.find hex ∈ Gp := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hjG
    exact htG hjG
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨t ^ 2 ^ i, T.pow_mem htT _, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_two, ← pow_mul, ← pow_succ]
  rw [hi] at hjG
  exact hjG

theorem burnsideF429a_T_inf_Gp [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hSG : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ T ∧ T ⊓ Gp = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := pCoreOf_le 2 _
  have hBn : M₁ ⊓ M₂ ≤ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG m,
        (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hm hxM) ((M₁ ⊓ M₂).inv_mem hm)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG m⁻¹
        simpa [mul_assoc] using this
      · have := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hm) hxM) hm
        simpa [mul_assoc] using this
  have hST : S ≤ T := by
    have h1 : S ≤ pCoreOf 2 (M₁ ⊓ M₂) :=
      le_pCoreOf_of_le_normalizer 2 (hSB.trans inf_le_right)
        (hBn.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    exact h1.trans (F7.isSylowTwoOf_pCoreOf_le hT)
  refine ⟨hST, le_antisymm ?_ (le_inf hST (hSB.trans inf_le_left))⟩
  have hSyl : ChF.IsSylowOf 2 S (Gp ⊓ (M₁ ⊓ M₂)) :=
    burnsideF429_isSylowOf_of_le hSG hSB inf_le_left
  have hle : T ⊓ Gp ≤ Gp ⊓ (M₁ ⊓ M₂) := fun x hx => ⟨hx.2, hT.1 hx.1⟩
  obtain ⟨x, hx, hconj⟩ := F7.isSylowTwoOf_exists_conj_le hSyl hle (hT.2.1.to_le inf_le_left)
  intro s hs
  have h1 : x⁻¹ * s * x ∈ S := mem_conjSub.1 (hconj hs)
  have hN := le_normalizer_pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) hx
  have := (Subgroup.mem_normalizer_iff.1 hN _).1 h1
  simpa [mul_assoc] using this

theorem burnsideF429a_sbar_le_oPPrime [Finite E] {Gp M₁ M₂ : Subgroup E} {P : Subgroup E}
    (hP : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ P) : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ oPPrime 2 P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hs
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (pCoreOf_isPGroup 2 (Gp ⊓ (M₁ ⊓ M₂)))) ⟨s, hs⟩
  exact Subgroup.subset_closure ⟨hP hs, k, by rw [← hk, Subgroup.orderOf_mk]⟩

theorem burnsideF429a_c5_of_key [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hSG : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp) {M : Subgroup E}
    (hM : M₁ ⊓ M₂ ≤ M) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂))
    (hkey : ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp) :
    pCoreOf 2 (oPPrime 2 (Gp ⊓ M) ⊔ T) = pCoreOf 2 (oPPrime 2 (Gp ⊓ M)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hST, hTinf⟩ := burnsideF429a_T_inf_Gp hSG hT
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set L := oPPrime 2 (Gp ⊓ M) with hLdef
  have hSGM : S ≤ Gp ⊓ M := (pCoreOf_le 2 _).trans (inf_le_inf_left _ hM)
  have hSyl : ChF.IsSylowOf 2 S (Gp ⊓ M) := burnsideF429_isSylowOf_of_le hSG hSGM inf_le_left
  have hSL : S ≤ L := burnsideF429a_sbar_le_oPPrime hSGM
  have hLP : L ≤ Gp ⊓ M := burnsideF429a_oPPrime_le _
  have hSylL : ChF.IsSylowOf 2 S L := burnsideF429_isSylowOf_of_le hSyl hSL hLP
  have hTP : T ≤ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have htM : t ∈ M := hM (hT.1 ht)
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG t,
        M.mul_mem (M.mul_mem htM hxM) (M.inv_mem htM)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG t⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem htM) hxM) htM
        simpa [mul_assoc] using this
  have hTL : T ≤ Subgroup.normalizer ((L : Subgroup E) : Set E) :=
    burnsideF429a_le_normalizer_oPPrime hTP
  have hLT : L ⊓ T = S := by
    refine le_antisymm (fun x hx => ?_) (le_inf hSL hST)
    rw [← hTinf]
    exact ⟨hx.2, (hLP hx.1).1⟩
  have hTsyl : ChF.IsSylowOf 2 T (L ⊔ T) := by
    refine ⟨le_sup_right, hT.2.1, ?_⟩
    rw [burnsideF429a_relIndex_sup hTL, hLT]
    exact hSylL.2.2
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hQT : Q ≤ T := F7.isSylowTwoOf_pCoreOf_le hTsyl
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
  have hQnorm : L ⊔ T ≤ Subgroup.normalizer ((Q : Subgroup E) : Set E) :=
    le_normalizer_pCoreOf 2 _
  have hOL : pCoreOf 2 L ≤ S := F7.isSylowTwoOf_pCoreOf_le hSylL
  have hQL : Q ⊓ L ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hQ2.to_le inf_le_left)
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hQnorm (Subgroup.mem_sup_left hl)) x
    constructor
    · rintro ⟨hxQ, hxL⟩
      exact ⟨h1.1 hxQ, L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)⟩
    · rintro ⟨hxQ, hxL⟩
      refine ⟨h1.2 hxQ, ?_⟩
      have := L.mul_mem (L.mul_mem (L.inv_mem hl) hxL) hl
      simpa [mul_assoc] using this
  apply le_antisymm
  · intro u hu
    have huT := hQT hu
    obtain ⟨k, hk⟩ := hT.2.1 ⟨u, huT⟩
    have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcomm : ∀ b ∈ L ⊓ (M₁ ⊓ M₂), u * b * u⁻¹ * b⁻¹ ∈ S := by
      intro b hb
      have h1 : u * b * u⁻¹ * b⁻¹ ∈ Q := by
        have hb' : b * u⁻¹ * b⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.1 (hQnorm (Subgroup.mem_sup_left hb.1)) _).1
            (Q.inv_mem hu)
        have := Q.mul_mem hu hb'
        simpa [mul_assoc] using this
      have h2 : u * b * u⁻¹ * b⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTL huT) b).1 hb.1) (L.inv_mem hb.1)
      exact hOL (hQL ⟨h1, h2⟩)
    have huG : u ∈ Gp := hkey u (hT.1 huT) k hk' hcomm
    have huS : u ∈ S := by
      rw [← hTinf]
      exact ⟨huT, huG⟩
    exact hQL ⟨hu, hSL huS⟩
  · refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 _)
    exact sup_le (le_normalizer_pCoreOf 2 _) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 _))

end Generic

end CFSG.ASVolI
