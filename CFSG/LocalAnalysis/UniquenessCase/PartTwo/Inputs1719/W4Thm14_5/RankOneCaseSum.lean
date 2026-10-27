module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ASetSummands
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.O4PlusUnique
import CFSG.Quasithin.Background.D36Support
import CFSG.Quasithin.Background.HLUBase
import CFSG.Quasithin.Background.StabSubBasics
import CFSG.Quasithin.Background.B2FactorizationSum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

private theorem map_conj_one_eq (K : Subgroup (MulAut W)) :
    K.map (MulAut.conj (1 : MulAut W)).toMonoidHom = K := by
  rw [map_one]
  exact Subgroup.map_id K

private theorem map_conj_map_conj_eq (K : Subgroup (MulAut W)) (x y : MulAut W) :
    (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      K.map (MulAut.conj (x * y)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem map_conj_eq_of_mem_normalizer {X : Subgroup (MulAut W)} {x : MulAut W}
    (hx : x ∈ normalizer (X : Set (MulAut W))) : X.map (MulAut.conj x).toMonoidHom = X := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx z).mp hz
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
    simpa using h

private theorem mem_normalizer_of_map_conj_eq {X : Subgroup (MulAut W)} {x : MulAut W}
    (h : X.map (MulAut.conj x).toMonoidHom = X) : x ∈ normalizer (X : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : x * z * x⁻¹ = x * y * x⁻¹ := hzy
    rw [mul_left_inj, mul_right_inj] at hzy'
    exact hzy' ▸ hz

private theorem map_conj_mem_conjSet_of_mem {K N X : Subgroup (MulAut W)} (hX : X ∈ conjSet K N)
    {x : MulAut W} (hx : x ∈ N) : X.map (MulAut.conj x).toMonoidHom ∈ conjSet K N := by
  obtain ⟨n, hn, rfl⟩ := hX
  exact ⟨x * n, N.mul_mem hx hn, map_conj_map_conj_eq K x n⟩

private theorem self_mem_conjSet (K N : Subgroup (MulAut W)) : K ∈ conjSet K N :=
  ⟨1, N.one_mem, (map_conj_one_eq K).symm⟩

private theorem le_of_mem_conjSet_of_le {K N X : Subgroup (MulAut W)} (hKN : K ≤ N)
    (hX : X ∈ conjSet K N) : X ≤ N := by
  obtain ⟨n, hn, rfl⟩ := hX
  rintro _ ⟨k, hk, rfl⟩
  simpa [MulAut.conj_apply] using N.mul_mem (N.mul_mem hn (hKN hk)) (N.inv_mem hn)

private theorem map_commV_eq (X : Subgroup (MulAut W)) (g : MulAut W) :
    (commV X).map g.toMonoidHom = commV (X.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rw [commV, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨x, hx, w, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, g w, ?_⟩
    simp [MulAut.mul_apply, map_mul, map_inv]
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, v, rfl⟩
    refine ⟨x (g⁻¹ v) * (g⁻¹ v)⁻¹, Subgroup.subset_closure ⟨x, hx, g⁻¹ v, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

private theorem apply_mem_commV_of_mem {X : Subgroup (MulAut W)} {x : MulAut W} (hx : x ∈ X)
    {u : W} (hu : u ∈ commV X) : x u ∈ commV X := by
  have h := map_commV_eq X x
  rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)] at h
  rw [← h]
  exact ⟨u, hu, rfl⟩

section Members

variable {Y L : Subgroup (MulAut W)}

private theorem commute_of_ne (hLY : L ≤ Y) (hsum : IsDirSumOver (conjSet L Y) commV)
    {X X' : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hX' : X' ∈ conjSet L Y) (hne : X ≠ X')
    {x y : MulAut W} (hx : x ∈ X) (hy : y ∈ X') : x * y = y * x := by
  have hE : (⊤ : Subgroup W) ≤ (x * y).toMonoidHom.eqLocus (y * x).toMonoidHom := by
    rw [← hsum.2]
    refine iSup_le fun Z u hu => ?_
    change x (y u) = y (x u)
    by_cases hZX : (Z : Subgroup (MulAut W)) = X
    · have hu' : u ∈ commV X := hZX ▸ hu
      rw [apply_eq_of_mem_commV hLY hsum.1 hX hX' hne hy hu',
        apply_eq_of_mem_commV hLY hsum.1 hX hX' hne hy (apply_mem_commV_of_mem hx hu')]
    · by_cases hZX' : (Z : Subgroup (MulAut W)) = X'
      · have hu' : u ∈ commV X' := hZX' ▸ hu
        rw [apply_eq_of_mem_commV hLY hsum.1 hX' hX (Ne.symm hne) hx hu',
          apply_eq_of_mem_commV hLY hsum.1 hX' hX (Ne.symm hne) hx (apply_mem_commV_of_mem hy hu')]
      · rw [apply_eq_of_mem_commV hLY hsum.1 Z.2 hX' hZX' hy hu,
          apply_eq_of_mem_commV hLY hsum.1 Z.2 hX hZX hx hu,
          apply_eq_of_mem_commV hLY hsum.1 Z.2 hX' hZX' hy hu]
  ext w
  exact hE (Subgroup.mem_top w)

private theorem le_normalizer_of_mem_conjSet (hLY : L ≤ Y) (hsum : IsDirSumOver (conjSet L Y) commV)
    {X X' : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hX' : X' ∈ conjSet L Y) :
    X' ≤ normalizer (X : Set (MulAut W)) := by
  by_cases h : X = X'
  · subst h
    exact Subgroup.le_normalizer
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc := commute_of_ne hLY hsum hX hX' h hx hy
      have : y * x * y⁻¹ = x := by rw [← hc]; group
      rw [this]
      exact hx
    · intro hx
      have hc := commute_of_ne hLY hsum hX hX' h hx hy
      have : x = y * x * y⁻¹ := by
        calc x = y⁻¹ * ((y * x * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [hc]
          _ = y * x * y⁻¹ := by group
      rw [this]
      exact hx

private theorem disjoint_commV_of_ne (hsum : IsDirSumOver (conjSet L Y) commV)
    {X X' : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hX' : X' ∈ conjSet L Y) (hne : X ≠ X') :
    Disjoint (commV X) (commV X') :=
  hsum.1.pairwiseDisjoint (i := ⟨X, hX⟩) (j := ⟨X', hX'⟩) fun h => hne (congrArg Subtype.val h)

end Members

private def permSub (𝒮 : Set (Subgroup (MulAut W))) : Subgroup (MulAut W) where
  carrier := {g | ∀ X, X ∈ 𝒮 ↔ X.map (MulAut.conj g).toMonoidHom ∈ 𝒮}
  one_mem' := fun X => by rw [map_conj_one_eq]
  mul_mem' := by
    intro a b ha hb X
    rw [← map_conj_map_conj_eq]
    exact (hb X).trans (ha _)
  inv_mem' := by
    intro g hg X
    have h := hg (X.map (MulAut.conj g⁻¹).toMonoidHom)
    rw [map_conj_map_conj_eq, mul_inv_cancel, map_conj_one_eq] at h
    exact h.symm

private theorem mem_permSub {𝒮 : Set (Subgroup (MulAut W))} {g : MulAut W} :
    g ∈ permSub 𝒮 ↔ ∀ X, X ∈ 𝒮 ↔ X.map (MulAut.conj g).toMonoidHom ∈ 𝒮 :=
  Iff.rfl

private theorem le_permSub_conjSet (K N : Subgroup (MulAut W)) : N ≤ permSub (conjSet K N) := by
  intro x hx X
  refine ⟨fun hX => map_conj_mem_conjSet_of_mem hX hx, fun hX => ?_⟩
  have h := map_conj_mem_conjSet_of_mem hX (N.inv_mem hx)
  rwa [map_conj_map_conj_eq, inv_mul_cancel, map_conj_one_eq] at h

private theorem le_permSub_of_le_normalizer {𝒮 : Set (Subgroup (MulAut W))}
    {K : Subgroup (MulAut W)} (hK : ∀ X ∈ 𝒮, K ≤ normalizer (X : Set (MulAut W))) :
    K ≤ permSub 𝒮 := by
  intro k hk X
  constructor
  · intro hX
    rwa [map_conj_eq_of_mem_normalizer (hK X hX hk)]
  · intro hX
    have h := map_conj_eq_of_mem_normalizer (hK _ hX (K.inv_mem hk))
    rw [map_conj_map_conj_eq, inv_mul_cancel, map_conj_one_eq] at h
    rwa [h]

private theorem le_stabSub_of_map_le {G : Subgroup (MulAut W)} {U : Subgroup W}
    (h : ∀ g ∈ G, U.map g.toMonoidHom ≤ U) : G ≤ stabSub U := by
  intro g hg u
  constructor
  · intro hu
    have := h g⁻¹ (G.inv_mem hg) ⟨g u, hu, rfl⟩
    simpa using this
  · intro hu
    exact h g hg ⟨u, hu, rfl⟩

private def sumIn (S 𝒯 : Set (Subgroup (MulAut W))) : Subgroup W :=
  ⨆ (X : S) (_ : (X : Subgroup (MulAut W)) ∈ 𝒯), commV (X : Subgroup (MulAut W))

private def sumOut (S 𝒯 : Set (Subgroup (MulAut W))) : Subgroup W :=
  ⨆ (X : S) (_ : (X : Subgroup (MulAut W)) ∉ 𝒯), commV (X : Subgroup (MulAut W))

private theorem disjoint_sumIn_sumOut [Finite W] {S : Set (Subgroup (MulAut W))}
    (h : IsDirSumOver S commV) (𝒯 : Set (Subgroup (MulAut W))) :
    Disjoint (sumIn S 𝒯) (sumOut S 𝒯) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite (Subgroup (MulAut W)) :=
    Finite.of_injective (fun K : Subgroup (MulAut W) => (K : Set (MulAut W))) SetLike.coe_injective
  exact h.1.disjoint_biSup_biSup' (s := {X : S | (X : Subgroup (MulAut W)) ∈ 𝒯})
    (t := {X : S | (X : Subgroup (MulAut W)) ∉ 𝒯})
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ h₁) (Set.toFinite _)

private theorem sumIn_sup_sumOut {S : Set (Subgroup (MulAut W))} (h : IsDirSumOver S commV)
    (𝒯 : Set (Subgroup (MulAut W))) : sumIn S 𝒯 ⊔ sumOut S 𝒯 = ⊤ := by
  rw [sumIn, sumOut, ← iSup_split, h.2]

private theorem sumIn_singleton {S : Set (Subgroup (MulAut W))} {L : Subgroup (MulAut W)}
    (hL : L ∈ S) : sumIn S {L} = commV L := by
  unfold sumIn
  apply le_antisymm
  · refine iSup₂_le fun X hX => ?_
    rw [Set.mem_singleton_iff] at hX
    rw [hX]
  · exact le_iSup₂_of_le (f := fun (X : S) (_ : (X : Subgroup (MulAut W)) ∈ ({L} : Set _)) =>
      commV (X : Subgroup (MulAut W))) ⟨L, hL⟩ rfl le_rfl

private theorem sumIn_pair {S : Set (Subgroup (MulAut W))} {L L' : Subgroup (MulAut W)}
    (hL : L ∈ S) (hL' : L' ∈ S) : sumIn S {L, L'} = commV L ⊔ commV L' := by
  unfold sumIn
  apply le_antisymm
  · refine iSup₂_le fun X hX => ?_
    rcases hX with hX | hX
    · rw [hX]
      exact le_sup_left
    · rw [Set.mem_singleton_iff] at hX
      rw [hX]
      exact le_sup_right
  · refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun (X : S) (_ : (X : Subgroup (MulAut W)) ∈ ({L, L'} : Set _)) =>
        commV (X : Subgroup (MulAut W))) ⟨L, hL⟩ (Or.inl rfl) le_rfl
    · exact le_iSup₂_of_le (f := fun (X : S) (_ : (X : Subgroup (MulAut W)) ∈ ({L, L'} : Set _)) =>
        commV (X : Subgroup (MulAut W))) ⟨L', hL'⟩ (Or.inr rfl) le_rfl

private theorem le_stabSub_sumIn (S 𝒯 : Set (Subgroup (MulAut W))) :
    permSub S ⊓ permSub 𝒯 ≤ stabSub (sumIn S 𝒯) := by
  refine le_stabSub_of_map_le fun g hg => ?_
  rw [sumIn, Subgroup.map_iSup]
  refine iSup_le fun X => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hX => ?_
  rw [map_commV_eq]
  exact le_iSup₂_of_le (f := fun (X : S) (_ : (X : Subgroup (MulAut W)) ∈ 𝒯) =>
    commV (X : Subgroup (MulAut W))) ⟨_, (mem_permSub.mp hg.1 _).mp X.2⟩
    ((mem_permSub.mp hg.2 _).mp hX) le_rfl

private theorem le_stabSub_sumOut (S 𝒯 : Set (Subgroup (MulAut W))) :
    permSub S ⊓ permSub 𝒯 ≤ stabSub (sumOut S 𝒯) := by
  refine le_stabSub_of_map_le fun g hg => ?_
  rw [sumOut, Subgroup.map_iSup]
  refine iSup_le fun X => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hX => ?_
  rw [map_commV_eq]
  exact le_iSup₂_of_le (f := fun (X : S) (_ : (X : Subgroup (MulAut W)) ∉ 𝒯) =>
    commV (X : Subgroup (MulAut W))) ⟨_, (mem_permSub.mp hg.1 _).mp X.2⟩
    (fun h => hX ((mem_permSub.mp hg.2 _).mpr h)) le_rfl

private theorem eq_of_mul_eq_mul {A B : Subgroup W} (hAB : Disjoint A B) {a a' b b' : W}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') : b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hmem : b' * b⁻¹ ∈ A ⊓ B :=
    ⟨h1 ▸ A.mul_mem (A.inv_mem ha') ha, B.mul_mem hb' (B.inv_mem hb)⟩
  rw [hAB.eq_bot, Subgroup.mem_bot] at hmem
  exact (mul_inv_eq_one.mp hmem).symm

section Orbit

variable {Y L T K : Subgroup (MulAut W)}

private theorem map_conj_le_of_mem (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom)
    {t : MulAut W} (ht : t ∈ T) : L.map (MulAut.conj t).toMonoidHom ≤ K :=
  hK ▸ le_iSup₂_of_le (f := fun t (_ : t ∈ T) => L.map (MulAut.conj t).toMonoidHom) t ht le_rfl

private theorem le_of_iSup_conj (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) : L ≤ K := by
  have h := map_conj_le_of_mem hK T.one_mem
  rwa [map_conj_one_eq] at h

private theorem iSup_conj_le (hLY : L ≤ Y) (hTY : T ≤ Y)
    (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) : K ≤ Y :=
  hK ▸ iSup₂_le fun t ht => le_of_mem_conjSet_of_le hLY ⟨t, hTY ht, rfl⟩

private theorem le_normalizer_of_mem_conjSet_T (hLY : L ≤ Y) (hTY : T ≤ Y)
    (hsum : IsDirSumOver (conjSet L Y) commV)
    (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) {X : Subgroup (MulAut W)}
    (hX : X ∈ conjSet L T) : K ≤ normalizer (X : Set (MulAut W)) := by
  obtain ⟨t₀, ht₀, rfl⟩ := hX
  exact hK ▸ iSup₂_le fun t ht =>
    le_normalizer_of_mem_conjSet hLY hsum ⟨t₀, hTY ht₀, rfl⟩ ⟨t, hTY ht, rfl⟩

private theorem map_conj_iSup_le (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom)
    {t : MulAut W} (ht : t ∈ T) : K.map (MulAut.conj t).toMonoidHom ≤ K := by
  conv_lhs => rw [hK]
  rw [Subgroup.map_iSup]
  refine iSup_le fun t' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ht' => ?_
  rw [map_conj_map_conj_eq]
  exact map_conj_le_of_mem hK (T.mul_mem ht ht')

private theorem le_centSub_sumOut (hLY : L ≤ Y) (hTY : T ≤ Y)
    (hsum : IsDirSumOver (conjSet L Y) commV)
    (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) :
    K ≤ centSub (sumOut (conjSet L Y) (conjSet L T)) := by
  rw [hK]
  refine iSup₂_le fun t ht x hx => mem_centSub.mpr fun u hu => ?_
  have hle : sumOut (conjSet L Y) (conjSet L T) ≤ fixV (L.map (MulAut.conj t).toMonoidHom) := by
    unfold sumOut
    refine iSup₂_le fun X hX v hv => mem_fixV.mpr fun y hy => ?_
    refine apply_eq_of_mem_commV hLY hsum.1 X.2 ⟨t, hTY ht, rfl⟩ ?_ hy hv
    rintro hXt
    exact hX (hXt ▸ ⟨t, ht, rfl⟩)
  exact mem_fixV.mp (hle hu) x hx

private theorem sup_le_permSub (hLY : L ≤ Y) (hTY : T ≤ Y)
    (hsum : IsDirSumOver (conjSet L Y) commV)
    (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) :
    K ⊔ T ≤ permSub (conjSet L T) :=
  sup_le (le_permSub_of_le_normalizer fun _ hX => le_normalizer_of_mem_conjSet_T hLY hTY hsum hK hX)
    (le_permSub_conjSet L T)

private theorem sup_le_permSub_Y (hLY : L ≤ Y) (hTY : T ≤ Y)
    (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) :
    K ⊔ T ≤ permSub (conjSet L Y) :=
  (sup_le (iSup_conj_le hLY hTY hK) hTY).trans (le_permSub_conjSet L Y)

private theorem fixV_le_w0 {W₀ : Subgroup W}
    (hW₀ : W₀ = ⨆ k ∈ K, (fixV T).map (k : MulAut W).toMonoidHom) : fixV T ≤ W₀ := by
  rw [hW₀]
  intro c hc
  exact Subgroup.mem_iSup_of_mem (1 : MulAut W) (Subgroup.mem_iSup_of_mem K.one_mem ⟨c, hc, rfl⟩)

private theorem sup_le_stabSub_w0 (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom)
    {W₀ : Subgroup W} (hW₀ : W₀ = ⨆ k ∈ K, (fixV T).map (k : MulAut W).toMonoidHom) :
    K ⊔ T ≤ stabSub W₀ := by
  refine sup_le (le_stabSub_of_map_le fun k hk => ?_) (le_stabSub_of_map_le fun t ht => ?_)
  · conv_lhs => rw [hW₀]
    rw [Subgroup.map_iSup]
    refine iSup_le fun k' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hk' => ?_
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [hW₀]
    exact Subgroup.mem_iSup_of_mem (k * k') (Subgroup.mem_iSup_of_mem (K.mul_mem hk hk')
      ⟨c, hc, rfl⟩)
  · conv_lhs => rw [hW₀]
    rw [Subgroup.map_iSup]
    refine iSup_le fun k' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hk' => ?_
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [hW₀]
    have hk'' : t * k' * t⁻¹ ∈ K :=
      map_conj_iSup_le hK ht ⟨k', hk', rfl⟩
    refine Subgroup.mem_iSup_of_mem (t * k' * t⁻¹) (Subgroup.mem_iSup_of_mem hk'' ⟨c, hc, ?_⟩)
    have htc : t⁻¹ c = c := mem_fixV.mp hc t⁻¹ (T.inv_mem ht)
    simp [MulAut.mul_apply, htc]

end Orbit

private theorem aParam_le_of_two_pieces {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {A B : Subgroup V}
    (hAB : Disjoint A B) (hAB' : A ⊔ B = ⊤)
    (hperm : ∀ x ∈ X, (A.map x.toMonoidHom = A ∧ B.map x.toMonoidHom = B) ∨
      (A.map x.toMonoidHom = B ∧ B.map x.toMonoidHom = A))
    {N : ℕ} (hN : 1 ≤ N) (hA : E3.aParam (autSub X A) ≤ N)
    (hB : E3.aParam (autSub X B) ≤ N) : E3.aParam X ≤ N := by
  let f : Bool → Subgroup V := fun b => cond b A B
  have hind : iSupIndep f :=
    (iSupIndep_pair (i := true) (j := false) (by decide) (fun b => by cases b <;> simp)).mpr hAB
  have htop : ⨆ b, f b = ⊤ := by
    rw [iSup_bool_eq]
    exact hAB'
  refine aParam_le_of_permutes hV hind htop (fun x hx b => ?_) hN (fun b => ?_)
  · rcases hperm x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases b
    · exact ⟨false, h2⟩
    · exact ⟨true, h1⟩
    · exact ⟨true, h2⟩
    · exact ⟨false, h1⟩
  · cases b
    · exact hB
    · exact hA

theorem aParam_autSub_eq_zero_of_fix {V : Type} [CommGroup V] {X : Subgroup (MulAut V)}
    {U : Subgroup V} (h : ∀ x ∈ X, ∀ u ∈ U, x u = u) : E3.aParam (autSub X U) = 0 := by
  have hbot : autSub X U = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨g, hgX, rfl⟩ := mem_autSub.mp hφ
    rw [Subgroup.mem_bot]
    ext u
    simp only [resHom_apply, MulAut.one_apply]
    exact h _ hgX _ u.2
  rw [hbot]
  simp [E3.aParam]

theorem aParam_autSub_autSub_le [Finite W] {X : Subgroup (MulAut W)} {V₀ U : Subgroup W}
    (hUV : U ≤ V₀) :
    E3.aParam (autSub (autSub X V₀) (U.subgroupOf V₀)) ≤ E3.aParam (autSub X U) := by
  rw [← H.aParam_map_congrHom (Subgroup.subgroupOfEquivOfLe hUV)]
  exact E3.aParam_mono (D36.map_autSub_autSub_le hUV)

private theorem aParam_autSub_map_eq [Finite W] {X : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ X) (M : Subgroup W) :
    E3.aParam (autSub X (M.map t.toMonoidHom)) = E3.aParam (autSub X M) := by
  have hX : X.map (H.congrHom t) = X := by
    have h : X.map (H.congrHom t) = X.map (MulAut.conj t).toMonoidHom := by
      congr 1
    rw [h, map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer ht)]
  have hU : ∀ v, v ∈ M ↔ t v ∈ M.map t.toMonoidHom := fun v =>
    ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, hwv⟩ => (t.injective hwv) ▸ hw⟩
  have h := H.LU.autSub_map t X hU
  rw [hX] at h
  rw [h, H.aParam_map_congrHom]

private theorem disjoint_subgroupOf {A B C : Subgroup W} (h : Disjoint A B) :
    Disjoint (A.subgroupOf C) (B.subgroupOf C) := by
  rw [Subgroup.disjoint_def] at h ⊢
  intro x hxA hxB
  exact Subtype.ext (h hxA hxB)

private theorem map_subgroupOf_resHom {V₀ N N' : Subgroup W} (hN : N ≤ V₀) (g : stabSub V₀)
    (hgN : N.map (g : MulAut W).toMonoidHom = N') :
    (N.subgroupOf V₀).map (resHom V₀ g).toMonoidHom = N'.subgroupOf V₀ := by
  ext v
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, ← hgN]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    exact ⟨⟨w, hN hw⟩, hw, Subtype.ext hwv⟩

private theorem map_inf_commV_eq {W₀ : Subgroup W} {g : MulAut W} (hg : g ∈ stabSub W₀)
    (X : Subgroup (MulAut W)) :
    (W₀ ⊓ commV X).map g.toMonoidHom = W₀ ⊓ commV (X.map (MulAut.conj g).toMonoidHom) := by
  rw [Subgroup.map_inf_eq _ _ _ g.injective, map_commV_eq, StabLat.mem_stabSub_iff_map.mp hg]

private theorem conjSet_eq_or [Finite W] {L T : Subgroup (MulAut W)}
    (hncard : (conjSet L T).ncard ≤ 2) :
    conjSet L T = {L} ∨ ∃ L' ∈ conjSet L T, L' ≠ L ∧ conjSet L T = {L, L'} := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite (Subgroup (MulAut W)) :=
    Finite.of_injective (fun K : Subgroup (MulAut W) => (K : Set (MulAut W))) SetLike.coe_injective
  by_cases h : ∀ X ∈ conjSet L T, X = L
  · left
    ext X
    rw [Set.mem_singleton_iff]
    exact ⟨h X, fun hX => hX ▸ self_mem_conjSet L T⟩
  · right
    push Not at h
    obtain ⟨L', hL', hne⟩ := h
    refine ⟨L', hL', hne, ?_⟩
    have hsub : ({L, L'} : Set (Subgroup (MulAut W))) ⊆ conjSet L T := by
      intro X hX
      rcases hX with hX | hX
      · exact hX ▸ self_mem_conjSet L T
      · rw [Set.mem_singleton_iff] at hX
        exact hX ▸ hL'
    have h2 : ({L, L'} : Set (Subgroup (MulAut W))).ncard = 2 := Set.ncard_pair hne.symm
    exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm

theorem aParam_autSub_le_of_inf_commV [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T K : Subgroup (MulAut W)} (hLY : L ≤ Y) (hTY : T ≤ Y)
    (hsum : IsDirSumOver (conjSet L Y) commV) (hncard : (conjSet L T).ncard ≤ 2)
    (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom)
    {W₀ : Subgroup W} (hW₀ : W₀ = ⨆ k ∈ K, (fixV T).map (k : MulAut W).toMonoidHom)
    (hclosed : ∀ u ∈ commV L, (∀ l ∈ L, l u * u⁻¹ ∈ W₀) → u ∈ W₀)
    {N : ℕ} (hN : 1 ≤ N) (hpiece : E3.aParam (autSub (K ⊔ T) (W₀ ⊓ commV L)) ≤ N) :
    E3.aParam (autSub (K ⊔ T) W₀) ≤ N := by
  classical
  set U₁ := sumIn (conjSet L Y) (conjSet L T) with hU₁
  set U₂ := sumOut (conjSet L Y) (conjSet L T) with hU₂
  have h12 : Disjoint U₁ U₂ := disjoint_sumIn_sumOut hsum _
  have h12' : U₁ ⊔ U₂ = ⊤ := sumIn_sup_sumOut hsum _
  have hperm := sup_le_permSub hLY hTY hsum hK
  have hpermY := sup_le_permSub_Y hLY hTY hK
  have hstU₁ : K ⊔ T ≤ stabSub U₁ := fun g hg => le_stabSub_sumIn _ _ ⟨hpermY hg, hperm hg⟩
  have hstU₂ : K ⊔ T ≤ stabSub U₂ := fun g hg => le_stabSub_sumOut _ _ ⟨hpermY hg, hperm hg⟩
  have hKU₂ := le_centSub_sumOut hLY hTY hsum hK
  have hstW₀ := sup_le_stabSub_w0 hK hW₀
  have hCW₀ := fixV_le_w0 hW₀
  have hL𝒳 : L ∈ conjSet L Y := self_mem_conjSet L Y
  have hcomp : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b ∈ fixV T → b ∈ fixV T := by
    intro a ha b hb hab
    refine mem_fixV.mpr fun t ht => ?_
    have htK : t ∈ K ⊔ T := Subgroup.mem_sup_right ht
    have h1 : t a * t b = a * b := by rw [← map_mul]; exact mem_fixV.mp hab t ht
    exact eq_of_mul_eq_mul h12 ((hstU₁ htK a).mpr ha) ha ((hstU₂ htK b).mpr hb) hb h1
  have hW₀le : W₀ ≤ (W₀ ⊓ U₁) ⊔ (fixV T ⊓ U₂) := by
    conv_lhs => rw [hW₀]
    refine iSup₂_le fun k hk => ?_
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (h12' ▸ Subgroup.mem_top c)
    have hbT : b ∈ fixV T := hcomp a ha b hb hc
    have hkb : k b = b := mem_centSub.mp (hKU₂ hk) b hb
    have hkc : k (a * b) ∈ W₀ := by
      rw [hW₀]
      exact Subgroup.mem_iSup_of_mem k (Subgroup.mem_iSup_of_mem hk ⟨_, hc, rfl⟩)
    have hka : k a ∈ W₀ := by
      have h := W₀.mul_mem hkc (W₀.inv_mem (hCW₀ hbT))
      rwa [map_mul, hkb, mul_inv_cancel_right] at h
    change k (a * b) ∈ _
    rw [map_mul, hkb]
    exact Subgroup.mul_mem_sup ⟨hka, (hstU₁ (Subgroup.mem_sup_left hk) a).mpr ha⟩ ⟨hbT, hb⟩
  have hBW₀ : fixV T ⊓ U₂ ≤ W₀ := inf_le_left.trans hCW₀
  have hW₀eq : (W₀ ⊓ U₁) ⊔ (fixV T ⊓ U₂) = W₀ := le_antisymm (sup_le inf_le_left hBW₀) hW₀le
  have hA₁ : E3.aParam (autSub (K ⊔ T) (W₀ ⊓ U₁)) ≤ N := by
    rcases conjSet_eq_or hncard with h𝒯 | ⟨L', hL'T, hL'L, h𝒯⟩
    ·
      have hU₁L : U₁ = commV L := by rw [hU₁, h𝒯, sumIn_singleton hL𝒳]
      rw [hU₁L]
      exact hpiece
    ·
      obtain ⟨t, ht, hL't⟩ := hL'T
      have hL'Y : L' ∈ conjSet L Y := ⟨t, hTY ht, hL't⟩
      have hLL' : L ≠ L' := fun h => hL'L h.symm
      have hU₁L : U₁ = commV L ⊔ commV L' := by rw [hU₁, h𝒯, sumIn_pair hL𝒳 hL'Y]
      have hdisjLL' : Disjoint (commV L) (commV L') := disjoint_commV_of_ne hsum hL𝒳 hL'Y hLL'
      have hdec : W₀ ⊓ U₁ = (W₀ ⊓ commV L) ⊔ (W₀ ⊓ commV L') := by
        apply le_antisymm
        · rintro w ⟨hw₀, hw₁⟩
          rw [hU₁L] at hw₁
          obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw₁
          have haW₀ : a ∈ W₀ := hclosed a ha fun l hl => by
            have hlb : l b = b :=
              apply_eq_of_mem_commV hLY hsum.1 hL'Y hL𝒳 (Ne.symm hLL') hl hb
            have hlw : l (a * b) ∈ W₀ :=
              (hstW₀ (Subgroup.mem_sup_left (le_of_iSup_conj hK hl)) _).mpr hw₀
            have h := W₀.mul_mem hlw (W₀.inv_mem hw₀)
            rwa [map_mul, hlb, mul_inv_rev, mul_assoc, mul_inv_cancel_left] at h
          have hbW₀ : b ∈ W₀ := by
            have h := W₀.mul_mem (W₀.inv_mem haW₀) hw₀
            rwa [inv_mul_cancel_left] at h
          exact Subgroup.mul_mem_sup ⟨haW₀, ha⟩ ⟨hbW₀, hb⟩
        · rw [hU₁L]
          exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
      have hMA : W₀ ⊓ commV L ≤ W₀ ⊓ U₁ := hdec ▸ le_sup_left
      have hM'A : W₀ ⊓ commV L' ≤ W₀ ⊓ U₁ := hdec ▸ le_sup_right
      have hstA : K ⊔ T ≤ stabSub (W₀ ⊓ U₁) := fun g hg u =>
        ⟨fun h => ⟨(hstW₀ hg u).mp h.1, (hstU₁ hg u).mp h.2⟩,
          fun h => ⟨(hstW₀ hg u).mpr h.1, (hstU₁ hg u).mpr h.2⟩⟩
      refine aParam_le_of_two_pieces (V := ↥(W₀ ⊓ U₁)) (fun w => Subtype.ext (hW w))
        (A := (W₀ ⊓ commV L).subgroupOf (W₀ ⊓ U₁))
        (B := (W₀ ⊓ commV L').subgroupOf (W₀ ⊓ U₁))
        (disjoint_subgroupOf (hdisjLL'.mono inf_le_right inf_le_right))
        (by rw [← Subgroup.subgroupOf_sup hMA hM'A, ← hdec, Subgroup.subgroupOf_self]) ?_ hN
        ((aParam_autSub_autSub_le hMA).trans hpiece) ?_
      · intro x hx
        obtain ⟨g, hgKT, rfl⟩ := mem_autSub.mp hx
        have hgW₀ : (g : MulAut W) ∈ stabSub W₀ := hstW₀ hgKT
        have hgperm := mem_permSub.mp (hperm hgKT)
        have hLg : L.map (MulAut.conj (g : MulAut W)).toMonoidHom ∈ ({L, L'} : Set _) :=
          h𝒯 ▸ (hgperm L).mp (self_mem_conjSet L T)
        have hL'g : L'.map (MulAut.conj (g : MulAut W)).toMonoidHom ∈ ({L, L'} : Set _) :=
          h𝒯 ▸ (hgperm L').mp (h𝒯 ▸ Or.inr rfl)
        have hinj : ∀ {X X' : Subgroup (MulAut W)},
            X.map (MulAut.conj (g : MulAut W)).toMonoidHom =
              X'.map (MulAut.conj (g : MulAut W)).toMonoidHom → X = X' := fun h =>
          Subgroup.map_injective (MulAut.conj (g : MulAut W)).injective h
        rcases hLg with hLg | hLg
        · have hL'g' : L'.map (MulAut.conj (g : MulAut W)).toMonoidHom = L' := by
            rcases hL'g with h | h
            · exact absurd (hinj (hLg.trans h.symm)) hLL'
            · exact h
          left
          exact ⟨map_subgroupOf_resHom hMA g ((map_inf_commV_eq hgW₀ L).trans (by rw [hLg])),
            map_subgroupOf_resHom hM'A g ((map_inf_commV_eq hgW₀ L').trans (by rw [hL'g']))⟩
        · rw [Set.mem_singleton_iff] at hLg
          have hL'g' : L'.map (MulAut.conj (g : MulAut W)).toMonoidHom = L := by
            rcases hL'g with h | h
            · exact h
            · rw [Set.mem_singleton_iff] at h
              exact absurd (hinj (hLg.trans h.symm)) hLL'
          right
          exact ⟨map_subgroupOf_resHom hMA g ((map_inf_commV_eq hgW₀ L).trans (by rw [hLg])),
            map_subgroupOf_resHom hM'A g ((map_inf_commV_eq hgW₀ L').trans (by rw [hL'g']))⟩
      · refine (aParam_autSub_autSub_le hM'A).trans ?_
        have htKT : t ∈ K ⊔ T := Subgroup.mem_sup_right ht
        have hM' : W₀ ⊓ commV L' = (W₀ ⊓ commV L).map t.toMonoidHom := by
          rw [map_inf_commV_eq (hstW₀ htKT) L, hL't]
        rw [hM', aParam_autSub_map_eq htKT]
        exact hpiece
  have hstA₁ : K ⊔ T ≤ stabSub (W₀ ⊓ U₁) := fun g hg u =>
    ⟨fun h => ⟨(hstW₀ hg u).mp h.1, (hstU₁ hg u).mp h.2⟩,
      fun h => ⟨(hstW₀ hg u).mpr h.1, (hstU₁ hg u).mpr h.2⟩⟩
  have hcentB : K ⊔ T ≤ centSub (fixV T ⊓ U₂) :=
    sup_le (fun k hk => mem_centSub.mpr fun u hu => mem_centSub.mp (hKU₂ hk) u hu.2)
      (fun t ht => mem_centSub.mpr fun u hu => mem_fixV.mp hu.1 t ht)
  refine aParam_le_of_two_pieces (V := ↥W₀) (fun w => Subtype.ext (hW w))
    (A := (W₀ ⊓ U₁).subgroupOf W₀) (B := (fixV T ⊓ U₂).subgroupOf W₀)
    (disjoint_subgroupOf (h12.mono inf_le_right inf_le_right))
    (by rw [← Subgroup.subgroupOf_sup inf_le_left hBW₀, hW₀eq, Subgroup.subgroupOf_self]) ?_ hN
    ((aParam_autSub_autSub_le inf_le_left).trans hA₁) ?_
  · intro x hx
    obtain ⟨g, hgKT, rfl⟩ := mem_autSub.mp hx
    left
    refine ⟨map_subgroupOf_resHom inf_le_left g
      (StabLat.mem_stabSub_iff_map.mp (hstA₁ hgKT)), map_subgroupOf_resHom hBW₀ g ?_⟩
    refine StabLat.mem_stabSub_iff_map.mp (centSub_le_stabSub _ (hcentB hgKT))
  · rw [aParam_autSub_eq_zero_of_fix]
    · omega
    · intro x hx u hu
      obtain ⟨g, hgKT, rfl⟩ := mem_autSub.mp hx
      exact Subtype.ext (mem_centSub.mp (hcentB hgKT) u hu)

theorem mem_normalizer_of_mem_stabSub_of_le_commV {Y L T K : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hTY : T ≤ Y) (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom)
    (hsum : IsDirSumOver (conjSet L Y) commV) {M : Subgroup W} (hM : M ≤ commV L)
    (hMne : M ≠ ⊥) {g : MulAut W} (hg : g ∈ K ⊔ T) (hgM : g ∈ stabSub M) :
    g ∈ normalizer (L : Set (MulAut W)) := by
  refine mem_normalizer_of_map_conj_eq ?_
  by_contra hne
  have hL𝒳 : L ∈ conjSet L Y := self_mem_conjSet L Y
  have hLg : L.map (MulAut.conj g).toMonoidHom ∈ conjSet L Y :=
    (mem_permSub.mp (sup_le_permSub_Y hLY hTY hK hg) L).mp hL𝒳
  have hdisj : Disjoint (commV L) (commV (L.map (MulAut.conj g).toMonoidHom)) :=
    disjoint_commV_of_ne hsum hL𝒳 hLg (Ne.symm hne)
  apply hMne
  rw [eq_bot_iff]
  intro m hm
  have hgm : m ∈ commV (L.map (MulAut.conj g).toMonoidHom) := by
    rw [← map_commV_eq]
    have hm' : g⁻¹ m ∈ M := (hgM (g⁻¹ m)).mp (by simpa using hm)
    exact ⟨g⁻¹ m, hM hm', by simp⟩
  exact Subgroup.disjoint_def.mp hdisj (hM hm) hgm

theorem stableUnder_inf_commV {L T K : Subgroup (MulAut W)}
    (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) {W₀ : Subgroup W}
    (hW₀ : W₀ = ⨆ k ∈ K, (fixV T).map (k : MulAut W).toMonoidHom) :
    StableUnder L (W₀ ⊓ commV L) := fun _ hl u hu =>
  ⟨(sup_le_stabSub_w0 hK hW₀ (Subgroup.mem_sup_left (le_of_iSup_conj hK hl)) u).mpr hu.1,
    apply_mem_commV_of_mem hl hu.2⟩

theorem iSup_conj_sup_le {Y L T K : Subgroup (MulAut W)} (hLY : L ≤ Y) (hTY : T ≤ Y)
    (hK : K = ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) : K ⊔ T ≤ Y :=
  sup_le (iSup_conj_le hLY hTY hK) hTY

theorem mem_of_forall_mul_inv_mem {L : Subgroup (MulAut W)} {M M' : Subgroup W}
    (hM : StableUnder L M) (hM' : StableUnder L M') (hMM' : M ⊓ M' = ⊥)
    (hM'fix : M' ⊓ fixV L = ⊥) {u : W} (hu : u ∈ M ⊔ M') (hcomm : ∀ l ∈ L, l u * u⁻¹ ∈ M) :
    u ∈ M := by
  obtain ⟨m, hm, m', hm', rfl⟩ := Subgroup.mem_sup.mp hu
  have hfix : m' ∈ M' ⊓ fixV L := by
    refine ⟨hm', mem_fixV.mpr fun l hl => ?_⟩
    have key : l (m * m') * (m * m')⁻¹ = (l m * m⁻¹) * (l m' * m'⁻¹) := by
      rw [map_mul]
      simp only [← div_eq_mul_inv]
      exact mul_div_mul_comm _ _ _ _
    have h1 : l m' * m'⁻¹ ∈ M := by
      have h := M.mul_mem (M.inv_mem (M.mul_mem (hM l hl m hm) (M.inv_mem hm))) (hcomm l hl)
      rwa [key, inv_mul_cancel_left] at h
    have h3 : l m' * m'⁻¹ ∈ M ⊓ M' := ⟨h1, M'.mul_mem (hM' l hl m' hm') (M'.inv_mem hm')⟩
    rw [hMM', Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.mp h3
  rw [hM'fix, Subgroup.mem_bot] at hfix
  rw [hfix, mul_one]
  exact hm

theorem commV_inf_fixV_eq_bot_of_dirSum {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hsum : IsDirSumOver (conjSet L Y) commV) (hfix : fixV (⨆ X ∈ conjSet L Y, X) = ⊥) :
    commV L ⊓ fixV L = ⊥ := by
  rw [eq_bot_iff, ← hfix]
  rintro u ⟨hu1, hu2⟩
  rw [mem_fixV]
  intro x hx
  have hmem : u ∈ fixV (⨆ X ∈ conjSet L Y, X) := by
    simp only [CFSG.Quasithin.fixV_iSup, Subgroup.mem_iInf]
    intro X hX
    by_cases hXL : X = L
    · subst hXL
      exact hu2
    · exact mem_fixV.mpr fun y hy =>
        apply_eq_of_mem_commV hLY hsum.1 (self_mem_conjSet L Y) hX (Ne.symm hXL) hy hu1
  exact mem_fixV.mp hmem x hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
