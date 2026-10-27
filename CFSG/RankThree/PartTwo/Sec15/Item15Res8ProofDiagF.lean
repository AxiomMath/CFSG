module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagA
import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag

open CFSG CFSG.ComponentClassification Equiv

variable {Γ : Type*} [Group Γ] [Finite Γ]

section Pair

variable {W W' : Subgroup Γ}

omit [Finite Γ] in
theorem comm_sup_of_comm (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {x : Γ}
    (hW : ∀ u ∈ W, u * x = x * u) (hW' : ∀ u ∈ W', u * x = x * u) {d : Γ} (hd : d ∈ W ⊔ W') :
    d * x = x * d := by
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_eq_of_mem_sup hc hd
  rw [mul_assoc, hW' w' hw', ← mul_assoc, hW w hw, mul_assoc]

omit [Finite Γ] in
theorem comm_left_of_comm_mul (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {u w w' : Γ}
    (hu : u ∈ W) (hw' : w' ∈ W') (h : u * (w * w') = w * w' * u) : u * w = w * u := by
  have h2 : w' * u = u * w' := (hc u hu w' hw').symm
  apply mul_right_cancel (b := w')
  calc u * w * w' = u * (w * w') := mul_assoc _ _ _
    _ = w * w' * u := h
    _ = w * (w' * u) := mul_assoc _ _ _
    _ = w * (u * w') := by rw [h2]
    _ = w * u * w' := (mul_assoc _ _ _).symm

omit [Finite Γ] in
theorem comm_right_of_comm_mul (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {u w w' : Γ}
    (hu : u ∈ W') (hw : w ∈ W) (h : u * (w * w') = w * w' * u) : u * w' = w' * u := by
  have h2 : w * u = u * w := hc w hw u hu
  apply mul_left_cancel (a := w)
  calc w * (u * w') = (w * u) * w' := (mul_assoc _ _ _).symm
    _ = (u * w) * w' := by rw [h2]
    _ = u * (w * w') := mul_assoc _ _ _
    _ = w * w' * u := h
    _ = w * (w' * u) := mul_assoc _ _ _

omit [Finite Γ] in
theorem exists_center_mul_of_comm (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {x : Γ}
    (hx : x ∈ W ⊔ W') (hW : ∀ u ∈ W, u * x = x * u) (hW' : ∀ u ∈ W', u * x = x * u) :
    ∃ z ∈ W, (∀ u ∈ W, u * z = z * u) ∧ ∃ z' ∈ W', (∀ u ∈ W', u * z' = z' * u) ∧
      x = z * z' := by
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_eq_of_mem_sup hc hx
  exact ⟨w, hw, fun u hu => comm_left_of_comm_mul hc hu hw' (hW u hu), w', hw',
    fun u hu => comm_right_of_comm_mul hc hu hw (hW' u hu), rfl⟩

omit [Finite Γ] in
theorem mem_of_comm_of_center_eq_bot (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w)
    (hZ : Subgroup.center ↥W = ⊥) {x : Γ} (hx : x ∈ W ⊔ W') (hxW : ∀ u ∈ W, u * x = x * u) :
    x ∈ W' := by
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_eq_of_mem_sup hc hx
  have hwc : (⟨w, hw⟩ : ↥W) ∈ Subgroup.center ↥W := by
    rw [Subgroup.mem_center_iff]
    intro u
    exact Subtype.ext (comm_left_of_comm_mul hc u.2 hw' (hxW u u.2))
  rw [hZ, Subgroup.mem_bot] at hwc
  have h1 : w = 1 := congrArg Subtype.val hwc
  rw [h1, one_mul]
  exact hw'

theorem le_normalizer_inf (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {Y : Subgroup Γ}
    (hYD : Y ≤ W ⊔ W') : Y ≤ Subgroup.normalizer ((Y ⊓ W : Subgroup Γ) : Set Γ) := fun _ hy =>
  mem_normalizer_of_conj_mem fun x hx =>
    ⟨Y.mul_mem (Y.mul_mem hy hx.1) (Y.inv_mem hy),
      (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_of_comm hc (hYD hy)) x).mp hx.2⟩

theorem inf_le_center (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {Y : Subgroup Γ}
    (hYD : Y ≤ W ⊔ W') (hYp : Group.IsPerfect Y)
    (hQ : ∀ N : Subgroup Γ, N ≤ Y → Y ≤ Subgroup.normalizer (N : Set Γ) →
      Group.IsSolvable N ∨ N = Y)
    (hYW : ¬ Y ≤ W)
    (hK1 : ∀ T S : Subgroup (↥W ⧸ Subgroup.center ↥W), Group.IsPerfect T → T ≠ ⊥ →
      Group.IsSolvable S → T ≤ Subgroup.normalizer (S : Set (↥W ⧸ Subgroup.center ↥W)) →
        S = ⊥)
    (hT1 : (Y.subgroupOf (W ⊔ W')).map (projQ hc) ≠ ⊥) {x : Γ} (hx : x ∈ Y ⊓ W) {u : Γ}
    (hu : u ∈ W) : u * x = x * u := by
  have hNs : Group.IsSolvable (Y ⊓ W : Subgroup Γ) := by
    rcases hQ (Y ⊓ W) inf_le_left (le_normalizer_inf hc hYD) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hYW
  set π := QuotientGroup.mk' (Subgroup.center ↥W) with hπ
  set S := ((Y ⊓ W).subgroupOf W).map π with hS
  have hSs : Group.IsSolvable S := by
    have := hNs
    have : Group.IsSolvable ((Y ⊓ W).subgroupOf W) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : Y ⊓ W ≤ W)).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
  have hTS : (Y.subgroupOf (W ⊔ W')).map (projQ hc) ≤
      Subgroup.normalizer (S : Set (↥W ⧸ Subgroup.center ↥W)) := by
    rintro _ ⟨y, hy, rfl⟩
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : Γ) ∈ Y ⊓ W := Subgroup.mem_subgroupOf.mp hs
    have hy' : (y : Γ) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hys : (y : Γ) * s * (y : Γ)⁻¹ ∈ Y ⊓ W :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_inf hc hYD hy') s).mp hs'
    have h1 := mk_conj_eq hc y s.2 hys.2
    rw [← h1]
    exact ⟨⟨_, hys.2⟩, Subgroup.mem_subgroupOf.mpr hys, rfl⟩
  have hSb := hK1 _ S (isPerfect_map_projQ hc hYD hYp) hT1 hSs hTS
  have h1 : π ⟨x, hx.2⟩ = 1 := by
    have h2 : π ⟨x, hx.2⟩ ∈ S := ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hSb, Subgroup.mem_bot] at h2
    exact h2
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h1
  exact congrArg Subtype.val (h1 ⟨u, hu⟩)

omit [Finite Γ] in
theorem mem_centralizer_of_fix (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w) {Y : Subgroup Γ}
    (hYD : Y ≤ W ⊔ W') (hYp : Group.IsPerfect Y) (hWp : Group.IsPerfect W)
    (hK2 : ∀ (σ : MulAut (↥W ⧸ Subgroup.center ↥W)) (k : ℕ), σ ^ (3 ^ k) = 1 →
      ∀ T : Subgroup (↥W ⧸ Subgroup.center ↥W), Group.IsPerfect T → T ≠ ⊥ →
        (∀ t ∈ T, σ t = t) → σ = 1)
    (hT1 : (Y.subgroupOf (W ⊔ W')).map (projQ hc) ≠ ⊥) {e : Γ}
    (heW : e ∈ Subgroup.normalizer (W : Set Γ)) (heW' : e ∈ Subgroup.normalizer (W' : Set Γ))
    (heY : e ∈ Subgroup.centralizer (Y : Set Γ)) {k : ℕ} (he : e ^ (3 ^ k) = 1) :
    e ∈ Subgroup.centralizer (W : Set Γ) := by
  have hσ : actQ W ⟨e, heW⟩ ^ (3 ^ k) = 1 := by
    rw [← map_pow]
    have h1 : (⟨e, heW⟩ : ↥(Subgroup.normalizer (W : Set Γ))) ^ (3 ^ k) = 1 :=
      Subtype.ext (by simpa using he)
    rw [h1, map_one]
  have hfix : ∀ t ∈ (Y.subgroupOf (W ⊔ W')).map (projQ hc), actQ W ⟨e, heW⟩ t = t := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : Γ) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hey : e * y * e⁻¹ = y := by
      rw [← Subgroup.mem_centralizer_iff.mp heY y hy']
      group
    have hx : e * (y : Γ) * e⁻¹ ∈ W ⊔ W' := by rw [hey]; exact y.2
    rw [← projQ_conj hc heW heW' y hx]
    congr 1
    exact Subtype.ext hey
  exact mem_centralizer_of_actQ_eq_one hWp
    (hK2 _ k hσ _ (isPerfect_map_projQ hc hYD hYp) hT1 hfix)

theorem mem_centralizer_of_mem_centralizer (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w)
    {Y : Subgroup Γ} (hYD : Y ≤ W ⊔ W') (hYp : Group.IsPerfect Y)
    (hQ : ∀ N : Subgroup Γ, N ≤ Y → Y ≤ Subgroup.normalizer (N : Set Γ) →
      Group.IsSolvable N ∨ N = Y)
    (hYW : ¬ Y ≤ W) (hWp : Group.IsPerfect W)
    (hK1 : ∀ T S : Subgroup (↥W ⧸ Subgroup.center ↥W), Group.IsPerfect T → T ≠ ⊥ →
      Group.IsSolvable S → T ≤ Subgroup.normalizer (S : Set (↥W ⧸ Subgroup.center ↥W)) →
        S = ⊥)
    (hK2 : ∀ (σ : MulAut (↥W ⧸ Subgroup.center ↥W)) (k : ℕ), σ ^ (3 ^ k) = 1 →
      ∀ T : Subgroup (↥W ⧸ Subgroup.center ↥W), Group.IsPerfect T → T ≠ ⊥ →
        (∀ t ∈ T, σ t = t) → σ = 1)
    (hT1 : (Y.subgroupOf (W ⊔ W')).map (projQ hc) ≠ ⊥) {e : Γ}
    (heY : e ∈ Subgroup.normalizer (Y : Set Γ)) (heW : e ∈ Subgroup.normalizer (W : Set Γ))
    (heW' : e ∈ Subgroup.normalizer (W' : Set Γ))
    (heC : e ∈ Subgroup.centralizer (W' : Set Γ)) {k : ℕ} (he : e ^ (3 ^ k) = 1) :
    e ∈ Subgroup.centralizer (W : Set Γ) := by
  have hcY : e ∈ Subgroup.centralizer (Y : Set Γ) := by
    apply mem_centralizer_of_displacement hYp heY
    intro y hy y' hy'
    have hd := displacement_mem hc hYD heY heW heC hy
    exact comm_sup_of_comm hc (fun u hu => inf_le_center hc hYD hYp hQ hYW hK1 hT1 hd hu)
      (fun u hu => (hc _ hd.2 u hu).symm) (hYD hy')
  exact mem_centralizer_of_fix hc hYD hYp hWp hK2 hT1 heW heW' hcY he

theorem le_normalizer_map_conj {D : Subgroup Γ} (hWD : D ≤ Subgroup.normalizer (W : Set Γ))
    {e : Γ} (heD : e ∈ Subgroup.normalizer (D : Set Γ)) :
    D ≤ Subgroup.normalizer ((W.map (MulAut.conj e).toMonoidHom : Subgroup Γ) : Set Γ) := by
  intro d hd
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨w, hw, rfl⟩
  have hd' : e⁻¹ * d * e ∈ D := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem heD) d).mp hd
    rwa [inv_inv] at h1
  have hw' : (e⁻¹ * d * e) * w * (e⁻¹ * d * e)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hWD hd') w).mp hw
  refine ⟨_, hw', ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem map_conj_eq_or_comm {D : Subgroup Γ} (hWD' : W ≤ D)
    (hWD : D ≤ Subgroup.normalizer (W : Set Γ)) (hW : IsSimpleGroup ↥W) {e : Γ}
    (heD : e ∈ Subgroup.normalizer (D : Set Γ)) :
    W.map (MulAut.conj e).toMonoidHom = W ∨
      ∀ a ∈ W.map (MulAut.conj e).toMonoidHom, ∀ b ∈ W, a * b = b * a := by
  set We := W.map (MulAut.conj e).toMonoidHom with hWe
  have hWeD : We ≤ D := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp heD w).mp (hWD' hw)
  have hsimp : IsSimpleGroup ↥We :=
    (W.equivMapOfInjective _ (MulAut.conj e).injective).symm.isSimpleGroup
  have hDWe := le_normalizer_map_conj hWD heD
  have hn : ((We ⊓ W).subgroupOf We).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro a ha
    apply mem_normalizer_of_conj_mem
    intro x hx
    exact ⟨We.mul_mem (We.mul_mem ha hx.1) (We.inv_mem ha),
      (Subgroup.mem_normalizer_iff.mp (hWD (hWeD ha)) x).mp hx.2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((We ⊓ W).subgroupOf We) with h | h
  · right
    intro a ha b hb
    have hab : a * b * a⁻¹ * b⁻¹ ∈ We ⊓ W := by
      refine ⟨?_, W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hWD (hWeD ha)) b).mp hb)
        (W.inv_mem hb)⟩
      have h1 : b * a⁻¹ * b⁻¹ ∈ We :=
        (Subgroup.mem_normalizer_iff.mp (hDWe (hWD' hb)) a⁻¹).mp (We.inv_mem ha)
      have h2 := We.mul_mem ha h1
      simpa [mul_assoc] using h2
    have h1 : (⟨_, hab.1⟩ : ↥We) ∈ (We ⊓ W).subgroupOf We := Subgroup.mem_subgroupOf.mpr hab
    rw [h, Subgroup.mem_bot] at h1
    have h2 : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  · left
    rw [Subgroup.subgroupOf_eq_top] at h
    refine Subgroup.eq_of_le_of_card_ge (h.trans inf_le_right) ?_
    rw [hWe, Subgroup.card_map_of_injective (MulAut.conj e).injective]

theorem mem_normalizer_of_partner (hc : ∀ w ∈ W, ∀ w' ∈ W', w * w' = w' * w)
    (hZ : Subgroup.center ↥W = ⊥) {e : Γ}
    (heD : e ∈ Subgroup.normalizer ((W ⊔ W' : Subgroup Γ) : Set Γ))
    (heW : e ∈ Subgroup.normalizer (W : Set Γ)) :
    e ∈ Subgroup.normalizer (W' : Set Γ) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  refine mem_of_comm_of_center_eq_bot hc hZ
    ((Subgroup.mem_normalizer_iff.mp heD x).mp (Subgroup.mem_sup_right hx)) fun u hu => ?_
  have hu' : e⁻¹ * u * e ∈ W := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem heW) u).mp hu
    rwa [inv_inv] at h1
  have h1 : (e⁻¹ * u * e) * x = x * (e⁻¹ * u * e) := hc _ hu' x hx
  calc u * (e * x * e⁻¹) = e * ((e⁻¹ * u * e) * x) * e⁻¹ := by group
    _ = e * (x * (e⁻¹ * u * e)) * e⁻¹ := by rw [h1]
    _ = e * x * e⁻¹ * u := by group

omit [Finite Γ] in
theorem map_eq_of_swap {U V : Subgroup Γ} (hUV : U ≠ V) {f : Γ ≃* Γ}
    (hf : ∀ x, f (f (f x)) = x)
    (hU : U.map f.toMonoidHom = U ∨ U.map f.toMonoidHom = V)
    (hV : V.map f.toMonoidHom = U ∨ V.map f.toMonoidHom = V) :
    U.map f.toMonoidHom = U ∧ V.map f.toMonoidHom = V := by
  have hinj : Function.Injective (Subgroup.map f.toMonoidHom) :=
    Subgroup.map_injective f.injective
  have hid : (f.toMonoidHom.comp f.toMonoidHom).comp f.toMonoidHom = MonoidHom.id Γ :=
    MonoidHom.ext hf
  have h3 : ∀ S : Subgroup Γ,
      ((S.map f.toMonoidHom).map f.toMonoidHom).map f.toMonoidHom = S := by
    intro S
    rw [Subgroup.map_map, Subgroup.map_map, hid, Subgroup.map_id]
  rcases hU with hU | hU
  · refine ⟨hU, ?_⟩
    rcases hV with hV | hV
    · exact absurd (hinj (hV.trans hU.symm)) hUV.symm
    · exact hV
  · exfalso
    rcases hV with hV | hV
    · have h := h3 U
      rw [hU, hV, hU] at h
      exact hUV h.symm
    · exact hUV (hinj (hU.trans hV.symm))

omit [Finite Γ] in
theorem conj_conj_conj {e : Γ} (he : e ^ 3 = 1) (x : Γ) :
    MulAut.conj e (MulAut.conj e (MulAut.conj e x)) = x := by
  simp only [MulAut.conj_apply]
  have he' : e * e * e = 1 := by rw [← pow_three', he]
  calc e * (e * (e * x * e⁻¹) * e⁻¹) * e⁻¹ = e * e * e * x * (e * e * e)⁻¹ := by group
    _ = x := by rw [he']; group

theorem mem_normalizer_of_map_eq {e : Γ} (h : W.map (MulAut.conj e).toMonoidHom = W) :
    e ∈ Subgroup.normalizer (W : Set Γ) :=
  mem_normalizer_of_conj_mem fun x hx => by
    rw [← h]
    exact ⟨x, hx, rfl⟩

end Pair

omit [Finite Γ] in
theorem isElemAbelian_zpowers {x : Γ} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem exists_elemAbelian_nine_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    ∃ F : Subgroup X, CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  classical
  set F₀ := KFacts.K412.eSix.subgroupOf (alternatingGroup (Fin 6)) with hF₀
  have hF₀9 : Nat.card F₀ = 9 := by
    rw [hF₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      KFacts.K412.eSix_le_alternatingGroup).toEquiv, KFacts.K412.card_eSix]
  have hF₀ab : CFSG.Assembly.IsElemAbelian 3 F₀ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, j, hij⟩ := Subgroup.mem_subgroupOf.mp a.2
      obtain ⟨k, l, hkl⟩ := Subgroup.mem_subgroupOf.mp b.2
      apply Subtype.ext
      apply Subtype.ext
      show ((a : alternatingGroup (Fin 6)) : Perm (Fin 6)) * b = b * a
      rw [hij, hkl]
      exact KFacts.K412.sixF_comm i j k l
    · obtain ⟨i, j, hij⟩ := Subgroup.mem_subgroupOf.mp hx
      apply Subtype.ext
      show ((x : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 3 = 1
      rw [hij]
      exact KFacts.K412.sixF_pow_three i j
  refine ⟨F₀.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hF₀ab _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hF₀9]

theorem exists_elemAbelian_nine_inf_center_eq_bot {X : Type*} [Group X] [Finite X]
    (htc : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) (hX : ¬ Group.IsPerfect X) :
    ∃ F : Subgroup X, CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
      F ⊓ Subgroup.center X = ⊥ := by
  obtain ⟨hZ3, ⟨φ⟩⟩ := htc
  set Z := Subgroup.center X with hZ
  set π := QuotientGroup.mk' Z with hπ
  set X' := commutator X with hX'
  have hA6 : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    Sec15.Y4Core.good3_alternatingGroup_six.1.1
  have hQp : Group.IsPerfect (X ⧸ Z) :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have hmap : X'.map π = ⊤ := by
    rw [hX', commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective Z)]
    exact hQp.commutator_eq_top
  have hsup : X' ⊔ Z = ⊤ := by
    have h1 := Subgroup.comap_map_eq π X'
    rw [hmap, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hinf : X' ⊓ Z = ⊥ := by
    by_contra hne
    have hdvd : Nat.card (X' ⊓ Z : Subgroup X) ∣ 3 :=
      hZ3 ▸ Subgroup.card_dvd_of_le inf_le_right
    have hne1 : Nat.card (X' ⊓ Z : Subgroup X) ≠ 1 := fun h1 =>
      hne (Subgroup.card_eq_one.mp h1)
    have h3 : Nat.card (X' ⊓ Z : Subgroup X) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hZX : Z ≤ X' := by
      have := Subgroup.eq_of_le_of_card_ge (inf_le_right : X' ⊓ Z ≤ Z) (by rw [h3, hZ3])
      rw [← this]
      exact inf_le_left
    apply hX
    rw [Group.isPerfect_def, ← hX']
    rw [sup_eq_left.mpr hZX] at hsup
    exact hsup
  have hinj : Function.Injective (π.comp X'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h1 : (x : X) ∈ X' ⊓ Z := ⟨x.2, hx⟩
    rw [hinf, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  have hsurj : Function.Surjective (π.comp X'.subtype) := by
    intro q
    have hq : q ∈ X'.map π := hmap ▸ Subgroup.mem_top q
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩
  set ψ : ↥X' ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.ofBijective _ ⟨hinj, hsurj⟩).trans φ with hψ
  obtain ⟨F₀, hF₀, hF₀9⟩ := exists_elemAbelian_nine_six ψ
  refine ⟨F₀.map X'.subtype, CFSG.SectionRank.isElemAbelian_map hF₀ _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X'.subtype_injective, hF₀9]
  · rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ X' ⊓ Z := ⟨Subgroup.map_subtype_le F₀ hx.1, hx.2⟩
    rwa [hinf] at h1

theorem exists_elemAbelian_nine_tripleCover' {X : Type*} [Group X] [Finite X]
    (htc : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) :
    ∃ F : Subgroup X, CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  by_cases hX : Group.IsPerfect X
  · exact exists_elemAbelian_nine_tripleCover hX htc
  · obtain ⟨F, hF, hF9, -⟩ := exists_elemAbelian_nine_inf_center_eq_bot htc hX
    exact ⟨F, hF, hF9⟩

end CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag
