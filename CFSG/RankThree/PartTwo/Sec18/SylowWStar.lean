module

public import CFSG.RankThree.PartTwo.Sec13.Item13Plane
public import CFSG.RankThree.PartTwo.KFacts.K74Bloom

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem quaternion_eq_or_sq_eq :
    ∀ g : QuaternionGroup 2, g ≠ 1 → g = QuaternionGroup.a 2 ∨ g ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem not_injective_quaternion
    (φ : QuaternionGroup 2 →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    ¬ Function.Injective φ := by
  intro hφ
  have hz1 : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have hsq : (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by decide
  have hZ2 : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
  have hsnd : (φ (QuaternionGroup.a 2)).2 ≠ 1 := by
    intro h
    apply hz1
    apply hφ
    rw [map_one]
    refine Prod.ext ?_ h
    rw [← hsq, map_pow, Prod.pow_fst, hZ2]
    rfl
  apply hsnd
  ext p
  rw [Equiv.Perm.one_apply]
  have hcard : Fintype.card (Fin 4) < Fintype.card (QuaternionGroup 2) := by
    rw [Fintype.card_fin, QuaternionGroup.card]
    norm_num
  obtain ⟨g, h, hgh, hp⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun g : QuaternionGroup 2 => (φ g).2 p) hcard
  have hp' : (φ g).2 p = (φ h).2 p := hp
  have hk : g⁻¹ * h ≠ 1 := fun e => hgh (inv_mul_eq_one.mp e)
  have hfix : (φ (g⁻¹ * h)).2 p = p := by
    rw [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, Equiv.Perm.mul_apply, ← hp',
      Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  rcases quaternion_eq_or_sq_eq _ hk with e | e
  · rw [← e, hfix]
  · rw [← e, map_pow, Prod.pow_snd, sq, Equiv.Perm.mul_apply, hfix, hfix]

variable {G : Type} [Group G]

structure PlaneQ8 (A B K : Subgroup G) (c : G) : Prop where
  isElemAbelian : CFSG.Assembly.IsElemAbelian 3 A
  card_eq : Nat.card A = 27
  mem : c ∈ A
  eq_sup : A = Subgroup.zpowers c ⊔ B
  not_mem : c ∉ B
  card_plane : Nat.card B = 9
  commute : ∀ k ∈ K, k * c = c * k
  irreducible : Sec21.IsIrreducibleOn (Sec4.autIn K B)
  le_normalizer : K ≤ Subgroup.normalizer (A : Set G)
  le_normalizer_plane : K ≤ Subgroup.normalizer (B : Set G)
  quaternion : ∃ f : QuaternionGroup 2 →* Sec4.autIn K A, Function.Injective f

@[expose] def StarNormalized (A K : Subgroup G) (c : G) : Prop :=
  ∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    ∀ k ∈ K, ∃ k' ∈ K, ∀ x ∈ A, (w * k * w⁻¹) * x * (w * k * w⁻¹)⁻¹ = k' * x * k'⁻¹

theorem starNormalized_of_le {A K : Subgroup G} {c : G}
    (h : Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (K : Set G)) :
    StarNormalized A K c := fun w hwA hwc k hk =>
  ⟨w * k * w⁻¹, (Subgroup.mem_normalizer_iff.mp (h ⟨hwA, hwc⟩) k).mp hk, fun _ _ => rfl⟩

section Helpers

variable [Finite G]

private theorem mem_normalizer_of_forall_conj_mem {V : Subgroup G} {g : G}
    (h : ∀ y ∈ V, g * y * g⁻¹ ∈ V) : g ∈ Subgroup.normalizer (V : Set G) := by
  let f : V → V := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hinj : Function.Injective f := by
    intro y y' hyy'
    have e : g * (y : G) * g⁻¹ = g * (y' : G) * g⁻¹ := congrArg Subtype.val hyy'
    exact Subtype.ext (by simpa using e)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨h y, fun hy => ?_⟩
  obtain ⟨y', hy'⟩ := hsurj ⟨g * y * g⁻¹, hy⟩
  have e : g * (y' : G) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hy'
  have e' : (y' : G) = y := by simpa using e
  exact e' ▸ y'.2

omit [Finite G] in
private theorem autIn_le_autIn {K H X : Subgroup G} (hKH : K ≤ H) :
    Sec4.autIn K X ≤ Sec4.autIn H X := by
  intro σ hσ
  obtain ⟨k, hkN, hkK, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  exact Sec4.mem_autIn_iff.mpr ⟨k, hkN, hKH hkK, rfl⟩

private theorem mem_normalizer_zpowers_of_conj_eq {w c : G} (h : w * c * w⁻¹ = c) :
    w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, h]
  exact Subgroup.zpow_mem_zpowers c k

end Helpers

section Plane

variable [Finite G] {A B K : Subgroup G} {c : G}

theorem mem_normalizer_plane_of (hP : PlaneQ8 A B K c) (hnorm : StarNormalized A K c) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwc : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    w ∈ Subgroup.normalizer (B : Set G) := by
  have hBA : B ≤ A := hP.eq_sup ▸ le_sup_right
  set V := B.map (MulAut.conj w).toMonoidHom with hVdef
  have hVA : V ≤ A := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hwA b).mp (hBA hb)
  have hwA' : w⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hwA
  have hwc' : w⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := Subgroup.inv_mem _ hwc
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := by
    intro k hk
    refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨k', hk'K, hk'⟩ := hnorm w⁻¹ hwA' hwc' k hk
    have e := hk' b (hBA hb)
    rw [inv_inv] at e
    refine ⟨k' * b * k'⁻¹, (Subgroup.mem_normalizer_iff.mp (hP.le_normalizer_plane hk'K) b).mp hb,
      ?_⟩
    change w * (k' * b * k'⁻¹) * w⁻¹ = k * (w * b * w⁻¹) * k⁻¹
    rw [← e]
    group
  have hcard : Nat.card V = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hP.card_plane]
  rcases Sec13.eq_of_le_of_le_normalizer hP.isElemAbelian hP.card_eq hP.mem hP.eq_sup hP.not_mem
      hP.card_plane hP.commute hP.irreducible hVA hKV hP.le_normalizer_plane with h | h | h | h
  · rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  · have h3 : Nat.card (Subgroup.zpowers c) = 3 := by
      rw [Nat.card_zpowers]
      have hc3 : c ^ 3 = 1 := hP.isElemAbelian.2 c hP.mem
      have hc1 : c ≠ 1 := fun e => hP.not_mem (e ▸ B.one_mem)
      exact orderOf_eq_prime hc3 hc1
    rw [h, h3] at hcard
    norm_num at hcard
  · refine mem_normalizer_of_forall_conj_mem fun b hb => ?_
    have : w * b * w⁻¹ ∈ V := ⟨b, hb, rfl⟩
    rwa [h] at this
  · rw [h, hP.card_eq] at hcard
    norm_num at hcard

theorem normalizer_le_normalizer_plane
    (hP : PlaneQ8 A B K c) (hnorm : StarNormalized A K c) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G) := by
  by_contra hWB
  by_cases hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  · exact hWB fun w hw => mem_normalizer_plane_of hP hnorm hw (hWc hw)
  have hA := hP.isElemAbelian
  have hBA : B ≤ A := hP.eq_sup ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x (hBA x.2) y (hBA y.2))⟩⟩, fun x hx => hA.2 x (hBA hx)⟩
  have hirrW := Sec13.isIrreducibleOn_wStar_of hA hP.card_eq hP.mem hP.eq_sup hP.not_mem
    hP.card_plane hP.commute hP.irreducible hP.le_normalizer hP.le_normalizer_plane hWc hWB
  have hKW : Sec4.autIn K A ≤ Sec13.wStar A := autIn_le_autIn le_top
  have h4 : 4 ∣ Nat.card (Sec13.wStar A) :=
    KFacts.four_dvd_card_of_irreducible_plane hBe hP.card_plane hBA hP.le_normalizer
      hP.le_normalizer_plane hP.irreducible hKW
  obtain ⟨f, hf⟩ := hP.quaternion
  have hN1 : Sec4.autIn K A ≠ ⊥ := by
    intro h
    have h0 : ∀ x, f x = 1 := fun x =>
      Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp h _ (f x).2)
    have hz1 : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
    exact hz1 (hf ((h0 _).trans (h0 1).symm))
  have hNfix : ∀ n ∈ Sec4.autIn K A, n ⟨c, hP.mem⟩ = ⟨c, hP.mem⟩ := by
    intro n hn
    obtain ⟨l, hlN, hlK, rfl⟩ := Sec4.mem_autIn_iff.mp hn
    apply Subtype.ext
    rw [Sec13.normalizerMonoidHom_apply_val]
    change l * c * l⁻¹ = c
    rw [hP.commute l hlK, mul_inv_cancel_right]
  have hNB : ∀ n ∈ Sec4.autIn K A, ∀ x : A, n x * x⁻¹ ∈ B.subgroupOf A := by
    intro n hn x
    obtain ⟨l, hlN, hlK, rfl⟩ := Sec4.mem_autIn_iff.mp hn
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Sec13.normalizerMonoidHom_apply_val]
    obtain ⟨i, -, b, hb, hx⟩ := Sec13.exists_pow_mul_of_mem hA hP.mem hP.eq_sup x.2
    rw [hx]
    have hlc : l * c ^ i = c ^ i * l := (Commute.pow_right (hP.commute l hlK) i).eq
    have hbl : l * b * l⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hP.le_normalizer_plane hlK) b).mp hb
    have hci : c ^ i ∈ A := A.pow_mem hP.mem i
    have hy : l * b * l⁻¹ * b⁻¹ ∈ B := B.mul_mem hbl (B.inv_mem hb)
    have e1 : l * (c ^ i * b) * l⁻¹ * (c ^ i * b)⁻¹ =
        c ^ i * (l * b * l⁻¹ * b⁻¹) * (c ^ i)⁻¹ := by
      calc l * (c ^ i * b) * l⁻¹ * (c ^ i * b)⁻¹
          = (l * c ^ i) * b * l⁻¹ * b⁻¹ * (c ^ i)⁻¹ := by group
        _ = c ^ i * l * b * l⁻¹ * b⁻¹ * (c ^ i)⁻¹ := by rw [hlc]
        _ = c ^ i * (l * b * l⁻¹ * b⁻¹) * (c ^ i)⁻¹ := by group
    rw [e1, hcomm _ hci _ (hBA hy), mul_inv_cancel_right]
    exact hy
  have hnormW : ∀ σ ∈ Sec13.wStar A, σ ⟨c, hP.mem⟩ = ⟨c, hP.mem⟩ →
      ∀ n ∈ Sec4.autIn K A, σ * n * σ⁻¹ ∈ Sec4.autIn K A := by
    intro σ hσ hσc n hn
    obtain ⟨w, hwN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    obtain ⟨l, hlN, hlK, rfl⟩ := Sec4.mem_autIn_iff.mp hn
    have hwc : w * c * w⁻¹ = c := by
      have h1 := congrArg Subtype.val hσc
      rwa [Sec13.normalizerMonoidHom_apply_val] at h1
    obtain ⟨k', hk'K, hk'⟩ := hnorm w hwN (mem_normalizer_zpowers_of_conj_eq hwc) l hlK
    have hmem : w * l * w⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hwN hlN) (Subgroup.inv_mem _ hwN)
    have hprod : A.normalizerMonoidHom ⟨w, hwN⟩ * A.normalizerMonoidHom ⟨l, hlN⟩ *
        (A.normalizerMonoidHom ⟨w, hwN⟩)⁻¹ = A.normalizerMonoidHom ⟨w * l * w⁻¹, hmem⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hprod]
    refine Sec4.mem_autIn_iff.mpr ⟨k', hP.le_normalizer hk'K, hk'K, ?_⟩
    ext x
    rw [Sec13.normalizerMonoidHom_apply_val, Sec13.normalizerMonoidHom_apply_val]
    exact (hk' x x.2).symm
  obtain ⟨-, φ, hφ⟩ := KFacts.rank3II_13_2_bloom hA hP.card_eq hirrW h4 (c := ⟨c, hP.mem⟩)
    (B := B.subgroupOf A) (fun h => hP.not_mem (Subgroup.mem_subgroupOf.mp h)) hN1 hNfix hNB
    hnormW
  exact not_injective_quaternion ((φ.comp (Subgroup.inclusion hKW)).comp f)
    (hφ.comp ((Subgroup.inclusion_injective hKW).comp hf))

theorem wStar_structure
    (hP : PlaneQ8 A B K c) (hnorm : StarNormalized A K c) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G) ∧
      (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∨
        (Sec13.oThreeWStar A = Sec13.transvAxis A B ∧ Nat.card (Sec13.oThreeWStar A) = 9 ∧
          Sec13.wStar A = Sec13.oThreeWStar A ⊔
            Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A ∧
          Sec13.orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) =
            Sec13.pointsOff A B ∧
          (Sec13.orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c)).ncard = 9)) := by
  have hWB := normalizer_le_normalizer_plane hP hnorm
  refine ⟨hWB, ?_⟩
  by_cases hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  · exact Or.inl hWc
  right
  have hA := hP.isElemAbelian
  have hc1 : c ≠ 1 := fun e => hP.not_mem (e ▸ (Subgroup.one_mem B))
  have hO3 := Sec13.oThreeWStar_eq_transvAxis hA hP.mem hP.eq_sup hP.not_mem hP.card_plane
    hP.commute hP.irreducible hP.le_normalizer hP.le_normalizer_plane hWB hWc
  obtain ⟨-, hT9⟩ := Sec13.transvAxis_le_wStar_and_card hA hP.mem hP.eq_sup hP.card_plane
    hP.commute hP.irreducible hP.le_normalizer hP.le_normalizer_plane hWB hWc
  have hcP : Subgroup.zpowers c ∈ Sec13.pointsOff A B :=
    (Sec13.mem_pointsOff_iff hA hP.mem hP.eq_sup hP.not_mem).mpr ⟨1, B.one_mem, by rw [mul_one]⟩
  have horbit : Sec13.orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) =
      Sec13.pointsOff A B := by
    ext F'
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Sec13.map_conj_mem_pointsOff hw (hWB hw) hcP
    · intro hF'
      obtain ⟨b', hb', rfl⟩ := (Sec13.mem_pointsOff_iff hA hP.mem hP.eq_sup hP.not_mem).mp hF'
      obtain ⟨w, hw, -, hwF⟩ := Sec13.exists_conj_pointsOff hA hP.mem hP.eq_sup hP.card_plane
        hP.commute hP.irreducible hP.le_normalizer hP.le_normalizer_plane hWB hWc B.one_mem hb'
      rw [mul_one] at hwF
      exact ⟨w, hw, hwF.symm⟩
  refine ⟨hO3, by rw [hO3, hT9], Sec13.wStar_eq_sup hA hP.mem hP.eq_sup hP.not_mem hP.card_plane
    hP.commute hP.irreducible hP.le_normalizer hP.le_normalizer_plane hWB hWc hP.mem hP.not_mem hc1,
    horbit, ?_⟩
  rw [horbit, Sec13.ncard_pointsOff hA hP.mem hP.eq_sup hP.not_mem hP.card_plane]

end Plane

end CFSG.RankThree.PartTwo.Sec18
