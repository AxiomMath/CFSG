module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs
import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofWeak

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

section Grp

theorem sylow_surj {N Γ : Type*} [Group N] [Finite N] [Group Γ] (f : N →* Γ)
    (hΓ : IsPGroup 2 Γ) (hf : Function.Surjective f) (S₀ : Subgroup N) (hS₀ : IsPGroup 2 S₀) :
    ∃ T : Subgroup N, IsPGroup 2 T ∧ S₀ ≤ T ∧ ∀ g : Γ, ∃ t ∈ T, f t = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS₀.exists_le_sylow
  refine ⟨P, P.isPGroup', hP, fun g => ?_⟩
  have hmax : (Sylow.mapSurjective hf P : Subgroup Γ) = ⊤ := by
    have h1 := (Sylow.mapSurjective hf P).is_maximal' (Q := ⊤) (hΓ.to_subgroup ⊤) le_top
    exact h1.symm
  have hg : g ∈ (Sylow.mapSurjective hf P : Subgroup Γ) := by
    rw [hmax]; exact Subgroup.mem_top g
  rw [Sylow.coe_mapSurjective] at hg
  obtain ⟨t, ht, rfl⟩ := hg
  exact ⟨t, ht, rfl⟩

theorem lift_two {N Γ : Type*} [Group N] [Finite N] [Group Γ] (ρ : N →* Γ)
    (R : Subgroup Γ) (hR : IsPGroup 2 R) (hRr : R ≤ ρ.range) (S₀ : Subgroup N)
    (hS₀ : IsPGroup 2 S₀) (hSR : ∀ s ∈ S₀, ρ s ∈ R) :
    ∃ T : Subgroup N, IsPGroup 2 T ∧ S₀ ≤ T ∧ ∀ r ∈ R, ∃ t ∈ T, ρ t = r := by
  set X : Subgroup N := R.comap ρ with hX
  let ρ' : X →* R := (ρ.comp X.subtype).codRestrict R (fun x => x.2)
  have hρ' : Function.Surjective ρ' := by
    rintro ⟨r, hr⟩
    obtain ⟨n, hn⟩ := hRr hr
    exact ⟨⟨n, show ρ n ∈ R from hn ▸ hr⟩, Subtype.ext hn⟩
  have hS₀X : S₀ ≤ X := fun s hs => hSR s hs
  have hS₀' : IsPGroup 2 (S₀.subgroupOf X) := by
    exact hS₀.comap_subtype (K := X)
  obtain ⟨T', hT'2, hT'S, hT'⟩ := sylow_surj ρ' (hR) hρ' (S₀.subgroupOf X) hS₀'
  refine ⟨T'.map X.subtype, hT'2.map _, ?_, ?_⟩
  · intro s hs
    exact ⟨⟨s, hS₀X hs⟩, hT'S (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
  · intro r hr
    obtain ⟨t, ht, htr⟩ := hT' ⟨r, hr⟩
    exact ⟨(t : N), ⟨t, ht, rfl⟩, congrArg Subtype.val htr⟩

end Grp

section LineQuat

variable {G : Type} [Group G] [Finite G]

theorem q8_rels :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 = QuaternionGroup.a 2 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 = QuaternionGroup.a 2 ∧
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 * (QuaternionGroup.xa 0 * QuaternionGroup.a 1) ∧
    (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 ∧
    (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide

theorem line_quat {A Le F Q L : Subgroup G} {c d e : G} (hF : IsFOf2127 A Le F)
    (hL : IsLOf2125 L c d e Le) (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)))
    (h28 : Concl2128 Le F Q) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ Le ⊓ Subgroup.normalizer (F : Set G) ∧
      ∃ a ∈ S, ∃ b ∈ S,
        (∀ m ∈ F ⊓ Le, a * (a * m * a⁻¹) * a⁻¹ = m⁻¹) ∧
        (∀ m ∈ F ⊓ Le, b * (b * m * b⁻¹) * b⁻¹ = m⁻¹) ∧
        (∀ m ∈ F ⊓ Le, a * (b * m * b⁻¹) * a⁻¹ = (b * (a * m * a⁻¹) * b⁻¹)⁻¹) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hM9, -⟩ := Item2119End8Proof.facts_H hF hL h26 h28
  obtain ⟨hFe, hF27, -, -, ⟨eQ8⟩⟩ := hF
  obtain ⟨-, hYtriv, -⟩ := h28
  have hVc : ∀ x y : F, x * y = y * x := fun x y => hFe.1.is_comm.comm x y
  have hV3 : ∀ x : F, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hFe.2 x x.2)
  have hQ8T : Sec4.autIn Le F ≤ Item2119End3Proof.fixQuot (Le.subgroupOf F) := by
    rw [← Item2119End3Proof.trivOnQuot_eq_fixQuot]
    refine le_trans (Item2119End3Proof.autIn_le_of_le ?_) hYtriv
    exact (le_sup_left : Le ⊓ Subgroup.normalizer (F : Set G) ≤
      (Le ⊓ Subgroup.normalizer (F : Set G)) ⊔ Q)
  have hT9 : Nat.card (Le.subgroupOf F) = 9 := by
    have h1 : Nat.card ((Le.subgroupOf F).map F.subtype) = Nat.card (Le.subgroupOf F) :=
      Subgroup.card_map_of_injective F.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_comm] at h1
    rw [← h1]
    exact hM9
  set Q8 := Sec4.autIn Le F with hQ8
  set N' : Subgroup (Subgroup.normalizer (F : Set G)) :=
    (Le ⊓ Subgroup.normalizer (F : Set G)).subgroupOf (Subgroup.normalizer (F : Set G))
    with hN'
  let ψ : N' →* Q8 :=
    (F.normalizerMonoidHom.comp N'.subtype).codRestrict Q8 (fun x => ⟨x, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hQ8card : Nat.card Q8 = 2 ^ 3 := by
    rw [Nat.card_congr eQ8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hQ82 : IsPGroup 2 Q8 := IsPGroup.of_card hQ8card
  have hbot : IsPGroup 2 (⊥ : Subgroup N') := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨T, hT2, -, hT⟩ := sylow_surj ψ hQ82 hψ ⊥ hbot
  set ga : Q8 := eQ8.symm (QuaternionGroup.a 1) with hga
  set gb : Q8 := eQ8.symm (QuaternionGroup.xa 0) with hgb
  set z : Q8 := eQ8.symm (QuaternionGroup.a 2) with hz
  obtain ⟨r1, r2, r3, r4, r5⟩ := q8_rels
  have hgaga : ga * ga = z := eQ8.injective (by
    rw [map_mul, hga, hz, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact r1)
  have hgbgb : gb * gb = z := eQ8.injective (by
    rw [map_mul, hgb, hz, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact r2)
  have hgagb : ga * gb = z * (gb * ga) := eQ8.injective (by
    rw [map_mul, map_mul, map_mul, hga, hgb, hz, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact r3)
  have hzz : z * z = 1 := eQ8.injective (by
    rw [map_mul, hz, MulEquiv.apply_symm_apply, map_one]; exact r4)
  have hz1 : z ≠ 1 := fun h => r5 (by
    have := congrArg eQ8 h
    rwa [hz, MulEquiv.apply_symm_apply, map_one] at this)
  have hzinv : ∀ v ∈ Le.subgroupOf F, (z : MulAut F) v = v⁻¹ := fun v hv =>
    Item2119End3Proof.apply_eq_inv_of_mem hVc hV3 hT9 (hQ8T z.2) (hQ8T ga.2)
      (fun h => hz1 (Subtype.ext h)) (by simpa using congrArg Subtype.val hzz)
      (by simpa using congrArg Subtype.val hgaga) hv
  obtain ⟨ta, hta, hψa⟩ := hT ga
  obtain ⟨tb, htb, hψb⟩ := hT gb
  set a : G := (((ta : N') : Subgroup.normalizer (F : Set G)) : G) with ha
  set b : G := (((tb : N') : Subgroup.normalizer (F : Set G)) : G) with hb
  have hσa : ∀ x : F, ((ga : MulAut F) x : G) = a * x * a⁻¹ := fun x => by
    have := congrArg (fun q : Q8 => ((q : MulAut F) x : G)) hψa
    exact this.symm
  have hσb : ∀ x : F, ((gb : MulAut F) x : G) = b * x * b⁻¹ := fun x => by
    have := congrArg (fun q : Q8 => ((q : MulAut F) x : G)) hψb
    exact this.symm
  refine ⟨((T.map N'.subtype).map (Subgroup.normalizer (F : Set G)).subtype),
    (hT2.map _).map _, ?_, a, ⟨_, ⟨ta, hta, rfl⟩, rfl⟩, b, ⟨_, ⟨tb, htb, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact t.2
  · intro m hm
    have hv : (⟨m, hm.1⟩ : F) ∈ Le.subgroupOf F := Subgroup.mem_subgroupOf.mpr hm.2
    have h1 := hzinv _ hv
    rw [← hgaga, Subgroup.coe_mul, MulAut.mul_apply] at h1
    have h2 := congrArg (fun x : F => (x : G)) h1
    simp only [hσa] at h2
    exact h2
  · intro m hm
    have hv : (⟨m, hm.1⟩ : F) ∈ Le.subgroupOf F := Subgroup.mem_subgroupOf.mpr hm.2
    have h1 := hzinv _ hv
    rw [← hgbgb, Subgroup.coe_mul, MulAut.mul_apply] at h1
    have h2 := congrArg (fun x : F => (x : G)) h1
    simp only [hσb] at h2
    exact h2
  · intro m hm
    have hv : (⟨m, hm.1⟩ : F) ∈ Le.subgroupOf F := Subgroup.mem_subgroupOf.mpr hm.2
    have hv' : ((gb : MulAut F) ((ga : MulAut F) ⟨m, hm.1⟩)) ∈ Le.subgroupOf F :=
      Item2119End3Proof.apply_mem_of_mem_fixQuot (hQ8T gb.2)
        (Item2119End3Proof.apply_mem_of_mem_fixQuot (hQ8T ga.2) hv)
    have h1 := hzinv _ hv'
    have h3 : ((ga : MulAut F) ((gb : MulAut F) ⟨m, hm.1⟩)) =
        (z : MulAut F) ((gb : MulAut F) ((ga : MulAut F) ⟨m, hm.1⟩)) := by
      have := congrArg (fun q : Q8 => ((q : MulAut F) ⟨m, hm.1⟩)) hgagb
      simpa [Subgroup.coe_mul, MulAut.mul_apply] using this
    have h4 : ((ga : MulAut F) ((gb : MulAut F) ⟨m, hm.1⟩) : F) =
        ((gb : MulAut F) ((ga : MulAut F) ⟨m, hm.1⟩))⁻¹ := by rw [h3, h1]
    have h5 := congrArg (fun x : F => (x : G)) h4
    simp only [hσa, hσb, Subgroup.coe_inv] at h5
    exact h5

end LineQuat

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
