module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsRank
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsMat

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open Matrix CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott (card_le_nine_mul_of_commute_mod)

section Group

variable {G : Type*} [Group G]

theorem card_map_eq_of_ker_eq {X Y : Type*} [Group X] [Group Y] (f₁ : G →* X) (f₂ : G →* Y)
    (h : ∀ g, f₁ g = 1 ↔ f₂ g = 1) (H : Subgroup G) :
    Nat.card (H.map f₁) = Nat.card (H.map f₂) := by
  have hk : (f₁.comp H.subtype).ker = (f₂.comp H.subtype).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact h x
  have h₁ : H.map f₁ = (f₁.comp H.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h₂ : H.map f₂ = (f₂.comp H.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h₁, h₂]
  exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange (f₁.comp H.subtype)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivRange (f₂.comp H.subtype)))).toEquiv

theorem commute_of_mem_closure {X : Set G} (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) {a b : G}
    (ha : a ∈ Subgroup.closure X) (hb : b ∈ Subgroup.closure X) : a * b = b * a := by
  have hXc : Subgroup.closure X ≤ Subgroup.centralizer X :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hX y hy x hx
  have hXa : Subgroup.closure X ≤ Subgroup.centralizer {a} := by
    refine (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr ?_
    rintro y rfl
    exact (Subgroup.mem_centralizer_iff.mp (hXc ha) x hx).symm
  exact Subgroup.mem_centralizer_iff.mp (hXa hb) a rfl

theorem pow_three_of_mem_closure {X : Set G} (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hX3 : ∀ x ∈ X, x ^ 3 = 1) {a : G} (ha : a ∈ Subgroup.closure X) : a ^ 3 = 1 := by
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hX3 x hx
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (commute_of_mem_closure hX hx hy) 3), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem conj_injective_of_center {S : Type*} [Group S]
    (hZ : ∀ s : S, (∀ t : S, s * t = t * s) → s = 1) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  apply hZ s
  intro t
  have h := congrArg (fun φ : MulAut S => φ t) hs
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc s * t = s * t * s⁻¹ * s := by group
    _ = t * s := by rw [h]

theorem center_trivial_of_isSimpleGroup {S : Type*} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : ∀ s : S, (∀ t : S, s * t = t * s) → s = 1 := by
  intro s hs'
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · have hm : s ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun t => (hs' t).symm
    rw [h] at hm
    exact (Subgroup.mem_bot).mp hm
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem false_of_fix_e9 {S : Type*} [Group S] [Finite S] (D : Subgroup (MulAut S))
    (hD : ∀ B ≤ D, (∀ b ∈ B, b ^ 3 = 1) → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → Nat.card B ≤ 9)
    (hinn : ∀ s : S, MulAut.conj s ∈ D) (hZ : ∀ s : S, (∀ t : S, s * t = t * s) → s = 1)
    {α : MulAut S} (hαD : α ∈ D) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    {K E : Subgroup S} (hEK : E ≤ K) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE9 : Nat.card E = 9) (hfix : ∀ k ∈ K, α k = k)
    (hZK : ∀ z ∈ E, (∀ k ∈ K, z * k = k * z) → z = 1) : False := by
  set I : Subgroup (MulAut S) := E.map (MulAut.conj : S →* MulAut S) with hI
  have hinj := conj_injective_of_center hZ
  have hI9 : Nat.card I = 9 := by
    rw [hI, Subgroup.card_map_of_injective hinj, hE9]
  set X : Set (MulAut S) := insert α (I : Set (MulAut S)) with hX
  have hαI : ∀ y ∈ I, α * y = y * α := by
    rintro _ ⟨e, he, rfl⟩
    have h := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv α e
    rw [hfix e (hEK he)] at h
    calc α * MulAut.conj e = α * MulAut.conj e * α⁻¹ * α := by group
      _ = MulAut.conj e * α := by rw [h]
  have hII : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [← map_mul, ← map_mul, hEc e he e' he']
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact hαI y hy
    · exact (hαI x hx).symm
    · exact hII x hx y hy
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    rcases hx with rfl | ⟨e, he, rfl⟩
    · exact hα3
    · rw [← map_pow, hE3 e he, map_one]
  set B : Subgroup (MulAut S) := Subgroup.closure X with hB
  have hBD : B ≤ D := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | ⟨e, -, rfl⟩
    · exact hαD
    · exact hinn e
  have hB9 := hD B hBD (fun b hb => pow_three_of_mem_closure hXc hX3 hb)
    (fun a ha b hb => commute_of_mem_closure hXc ha hb)
  have hIB : I ≤ B := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have hIeq : I = B := Subgroup.eq_of_le_of_card_ge hIB (by rw [hI9]; exact hB9)
  have hαB : α ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  rw [← hIeq] at hαB
  obtain ⟨e, he, rfl⟩ := hαB
  apply hα1
  have he1 : e = 1 := by
    refine hZK e he (fun k hk => ?_)
    have h := hfix k hk
    simp only [MonoidHom.coe_coe, MulAut.conj_apply] at h
    calc e * k = e * k * e⁻¹ * e := by group
      _ = k * e := by rw [h]
  rw [he1, map_one]

theorem false_of_fix_e9_of_mulEquiv {S X : Type*} [Group S] [Group X] [Finite X] (τ : S ≃* X)
    (D : Subgroup (MulAut X))
    (hD : ∀ B ≤ D, (∀ b ∈ B, b ^ 3 = 1) → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → Nat.card B ≤ 9)
    (hinn : ∀ s : X, MulAut.conj s ∈ D) (hZ : ∀ s : X, (∀ t : X, s * t = t * s) → s = 1)
    {σ : MulAut S} (hσD : MulAut.congr τ σ ∈ D) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {K E : Subgroup S} (hEK : E ≤ K) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE9 : Nat.card E = 9) (hfix : ∀ k ∈ K, σ k = k)
    (hZK : ∀ z ∈ E, (∀ k ∈ K, z * k = k * z) → z = 1) : False := by
  refine false_of_fix_e9 D hD hinn hZ hσD (by rw [← map_pow, hσ3, map_one])
    (fun h => hσ1 ((MulAut.congr τ).injective (by rw [h, map_one])))
    (K := K.map τ.toMonoidHom) (E := E.map τ.toMonoidHom) (Subgroup.map_mono hEK) ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE3 a ha, map_one]
  · rw [Subgroup.card_map_of_injective τ.injective, hE9]
  · rintro _ ⟨k, hk, rfl⟩
    show τ (σ (τ.symm (τ k))) = τ k
    rw [MulEquiv.symm_apply_apply, hfix k hk]
  · rintro _ ⟨z, hz, rfl⟩ hcomm
    have hz1 : z = 1 := by
      refine hZK z hz (fun k hk => τ.injective ?_)
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hcomm (τ k) ⟨k, hk, rfl⟩
    simp [hz1]

theorem card_le_nine_inn {X : Type*} [Group X] [Finite X]
    (hN : ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27)
    (hZ : ∀ s : X, (∀ t : X, s * t = t * s) → s = 1) {B : Subgroup (MulAut X)}
    (hB : B ≤ (MulAut.conj : X →* MulAut X).range) (h3 : ∀ b ∈ B, b ^ 3 = 1)
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := conj_injective_of_center hZ
  set B' := B.comap (MulAut.conj : X →* MulAut X) with hB'
  have hmap : B'.map (MulAut.conj : X →* MulAut X) = B := by
    rw [hB', Subgroup.map_comap_eq, inf_eq_right.mpr hB]
  have hcard : Nat.card B' = Nat.card B := by
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hB'c : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact hc _ ha _ hb
  have hB'3 : ∀ a ∈ B', a ^ 3 = 1 := by
    intro a ha
    apply hinj
    rw [map_pow, map_one]
    exact h3 _ ha
  rw [← hcard]
  by_contra hlt
  push Not at hlt
  have hp : IsPGroup 3 B' := fun x => ⟨1, Subtype.ext (by simpa using hB'3 _ x.2)⟩
  obtain ⟨j, hj⟩ := hp.exists_card_eq
  have hj3 : 3 ≤ j := by
    by_contra hj3
    push Not at hj3
    have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 3 ∣ Nat.card B' from hj ▸ Nat.pow_dvd_pow 3 hj3)
  refine hN (E₀.map B'.subtype) ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩ ?_
  · obtain ⟨_, ⟨a, -, rfl⟩⟩ := a
    obtain ⟨_, ⟨b, -, rfl⟩⟩ := b
    exact hB'c _ a.2 _ b.2
  · rintro _ ⟨a, -, rfl⟩
    exact hB'3 _ a.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective B'), hE₀]
    norm_num

end Group

section Rank

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem card_le_nine_of_le_range (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {S G : Type*} [Group S] [Group G] (c : G →* MulAut S) (ι : G →* GL (Fin 3) K)
    (hker : ∀ g, c g = 1 ↔ ProjGenLinGroup.mk (ι g) = 1) (hH : ∀ g, ι g ∈ glPi π 3 (p ^ f) K)
    {B : Subgroup (MulAut S)} (hB : B ≤ c.range) (h3 : ∀ b ∈ B, b ^ 3 = 1)
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 9 := by
  have := hK.finite
  set H : Subgroup G := B.comap c with hHdef
  set T : Subgroup (GL (Fin 3) K) := H.map ι with hTdef
  have hT3 : ∀ t ∈ T, t ^ 3 ∈ StatedScalars (Fin 3) K := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, ← mk_eq_one_iff_mem_statedScalars, ← hker, map_pow]
    exact h3 _ hg
  have hTc : ∀ t ∈ T, ∀ u ∈ T, t * u * t⁻¹ * u⁻¹ ∈ StatedScalars (Fin 3) K := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      ← mk_eq_one_iff_mem_statedScalars, ← hker, map_mul, map_mul, map_mul, map_inv, map_inv,
      hc _ hg _ hg']
    group
  have hTH : T ≤ glPi π 3 (p ^ f) K := by
    rintro _ ⟨g, -, rfl⟩
    exact hH g
  have hle := card_le_nine_mul_of_commute_mod hK hq hTH hT3 hTc
  have hBH : H.map c = B := by
    rw [hHdef, Subgroup.map_comap_eq, inf_eq_right.mpr hB]
  have hmk : Nat.card (T.map (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K)) =
      Nat.card B := by
    rw [hTdef, Subgroup.map_map, ← hBH]
    exact (card_map_eq_of_ker_eq c _ hker H).symm
  set ψ : T →* ProjGenLinGroup (Fin 3) K :=
    (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).comp T.subtype with hψ
  have hψr : ψ.range = T.map (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hψk : ψ.ker = (StatedScalars (Fin 3) K).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, MonoidHom.comp_apply,
      Subgroup.coe_subtype, mk_eq_one_iff_mem_statedScalars]
  have hcardT : Nat.card T = Nat.card B * Nat.card ↥(T ⊓ StatedScalars (Fin 3) K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hψr, hmk, hψk,
      ← Subgroup.inf_subgroupOf_right, inf_comm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hpos : 0 < Nat.card ↥(T ⊓ StatedScalars (Fin 3) K) := Nat.card_pos
  rw [hcardT] at hle
  exact Nat.le_of_mul_le_mul_right hle hpos

end Rank

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
