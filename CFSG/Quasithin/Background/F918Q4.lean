module

public import CFSG.Quasithin.Background.F918H1

public section

namespace CFSG.Quasithin

section AuxQ4

variable {W : Type} [CommGroup W]

private theorem mul_inv_mem_of_perfectQ4 [Finite W] {L : Subgroup (MulAut W)} [Group.IsPerfect ↥L]
    {U D : Subgroup W} (hLU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hLD : ∀ l ∈ L, ∀ d ∈ D, l d = d)
    (hcard : (D.subgroupOf U).index ≤ 4) : ∀ l ∈ L, ∀ u ∈ U, l u * u⁻¹ ∈ D := by
  let D' : Subgroup ↥U := D.subgroupOf U
  let φ : ↥L → ↥U →* ↥U := fun l =>
    { toFun := fun u => ⟨(l : MulAut W) u, hLU l l.2 u u.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hφ : ∀ l : ↥L, D' ≤ D'.comap (φ l) := fun l d hd => by
    show (l : MulAut W) (d : W) ∈ D
    rw [hLD l l.2 d hd]
    exact hd
  let _ : MulAction ↥L (↥U ⧸ D') :=
    { smul := fun l => QuotientGroup.map D' D' (φ l) (hφ l)
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H u => exact congrArg QuotientGroup.mk (Subtype.ext rfl)
      mul_smul := fun a b q => by
        induction q using QuotientGroup.induction_on with
        | H u => exact congrArg QuotientGroup.mk (Subtype.ext rfl) }
  let ρ : ↥L →* Equiv.Perm (↥U ⧸ D') := MulAction.toPermHom ↥L (↥U ⧸ D')
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have : Group.IsSolvable (Equiv.Perm (↥U ⧸ D')) := Equiv.Perm.isSolvable hcard
  have hsub : Subsingleton ρ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ρ.range inferInstance
  intro l hl u hu
  have h1 : ρ ⟨l, hl⟩ = 1 := by
    have : (⟨ρ ⟨l, hl⟩, ⟨l, hl⟩, rfl⟩ : ρ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have h2 : (QuotientGroup.mk (φ ⟨l, hl⟩ ⟨u, hu⟩) : ↥U ⧸ D') = QuotientGroup.mk ⟨u, hu⟩ :=
    congrArg (fun e : Equiv.Perm (↥U ⧸ D') => e (QuotientGroup.mk ⟨u, hu⟩)) h1
  have h3 : (φ ⟨l, hl⟩ ⟨u, hu⟩)⁻¹ * ⟨u, hu⟩ ∈ D' := QuotientGroup.eq.mp h2
  have h3' : (l u)⁻¹ * u ∈ D := h3
  have e : l u * u⁻¹ = ((l u)⁻¹ * u)⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
  rw [e]
  exact inv_mem h3'

private theorem mul_inv_mem_of_supQ4 {Mp L L' : Subgroup (MulAut W)} {V E : Subgroup W}
    (hMp : Mp = L ⊔ L') (hinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V)
    (hL : ∀ l ∈ L, ∀ v ∈ V, l v * v⁻¹ ∈ E) (htriv : ∀ v ∈ V, ∀ g ∈ L', g v = v) :
    ∀ x ∈ Mp, ∀ v ∈ V, x v * v⁻¹ ∈ E := by
  let P : Subgroup (MulAut W) :=
    { carrier := {x | x ∈ Mp ∧ ∀ v ∈ V, x v * v⁻¹ ∈ E}
      one_mem' := ⟨Mp.one_mem, fun v _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨Mp.mul_mem haM hbM, fun v hv => ?_⟩
        have e : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [e]
        exact mul_mem (ha (b v) (hinv b hbM v hv)) (hb v hv)
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨Mp.inv_mem haM, fun v hv => ?_⟩
        have hw : a⁻¹ v ∈ V := hinv a⁻¹ (Mp.inv_mem haM) v hv
        have e : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
          rw [show a (a⁻¹ v) = v by simp]
          group
        rw [e]
        exact inv_mem (ha (a⁻¹ v) hw) }
  have hLMp : L ≤ Mp := by rw [hMp]; exact le_sup_left
  have hL'Mp : L' ≤ Mp := by rw [hMp]; exact le_sup_right
  have hLP : L ≤ P := fun l hl => ⟨hLMp hl, hL l hl⟩
  have hL'P : L' ≤ P := fun g hg => ⟨hL'Mp hg, fun v hv => by rw [htriv v hv g hg]; simp⟩
  have hMpP : Mp ≤ P := by rw [hMp]; exact sup_le hLP hL'P
  exact fun x hx => (hMpP hx).2

private theorem rk_add_two_lt_of_perfectQ4 [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    {Mp L L' : Subgroup (MulAut W)} [Group.IsPerfect ↥L] {V U D : Subgroup W} (hMp : Mp = L ⊔ L')
    (hirr : V ∈ IrrPlus Mp (⊤ : Subgroup W)) (hVU : V ≤ U) (htriv : ∀ v ∈ V, ∀ g ∈ L', g v = v)
    (hLU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hDU : D ≤ U) (hDfix : ∀ x ∈ Mp, ∀ d ∈ D, x d = d) :
    rk ↥D + 2 < rk ↥U := by
  have hinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hirr.2.1 ⟨x, hx⟩ v hv
  have hLMp : L ≤ Mp := by rw [hMp]; exact le_sup_left
  by_contra hle
  rw [not_lt] at hle
  have hcard : (D.subgroupOf U).index ≤ 4 := by
    have h1 := Subgroup.card_mul_index (D.subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDU).toEquiv, card_eq_two_pow hexp D,
      card_eq_two_pow hexp U] at h1
    have h2 : 2 ^ rk ↥D * (D.subgroupOf U).index ≤ 2 ^ rk ↥D * 4 := by
      rw [h1]
      calc 2 ^ rk ↥U ≤ 2 ^ (rk ↥D + 2) := Nat.pow_le_pow_right (by norm_num) hle
        _ = 2 ^ rk ↥D * 4 := by rw [pow_add]; norm_num
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  have hLD := mul_inv_mem_of_perfectQ4 hLU (fun l hl d hd => hDfix l (hLMp hl) d hd) hcard
  have key := mul_inv_mem_of_supQ4 hMp hinv (fun l hl v hv => hLD l hl v (hVU hv)) htriv
  have hVD : V ≤ D := by
    have h : XMod.commOf ↥Mp V ≤ D :=
      (XMod.commOf_le_iff (A := ↥Mp)).mpr fun a v hv => key a.1 a.2 v hv
    rwa [hirr.2.2.1] at h
  exact not_le_of_gt hirr.2.2.2.1 fun v hv => ⟨hv, fun a => hDfix a.1 a.2 v (hVD hv)⟩

end AuxQ4

section D36Q4

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d36_rank_Y (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
        ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) + 2 <
      rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V)) := by
  have hUV : commSub (orbSup T V) L ≤ orbSup T V := by
    rw [d36_U_eq hL38 n]
    exact orbSup_le fun s hs => map_le_orbSup hs.1
  have hrk : ∀ J : Subgroup W, J ≤ orbSup T V → rk ↥(J.subgroupOf (orbSup T V)) = rk ↥J :=
    fun J hJ => by unfold rk; rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ).toEquiv]
  have hinf : (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
      ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) =
      (commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf
        (orbSup T V) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [hinf, hrk _ (inf_le_left.trans hUV), hrk _ hUV]
  have hLtU := (d36_part1 hL38 n).2
  have h1 : conjAutSub t⁻¹ L = conjAutSub t L := by
    rcases (hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq).2.2.2 t⁻¹ (T.inv_mem n.tT) with h | h
    · have h2 : t⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
      exact (n.tn (by simpa using inv_mem h2)).elim
    · exact h
  have hLUt : ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ L, g (t u) = t u := by
    intro u hu g hg
    have h3 : t⁻¹ * g * t ∈ conjAutSub t L := by
      rw [← h1, mem_conjAutSub_iff]
      simpa [mul_assoc] using hg
    calc g (t u) = t ((t⁻¹ * g * t) u) := by simp [MulAut.mul_apply]
      _ = t u := by rw [hLtU u hu _ h3]
  have hDfix : ∀ x ∈ Mp, ∀ d ∈ commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom,
      x d = d := by
    have hle : Mp ≤
        centSub (commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom) := by
      rw [n.Mp_eq]
      refine sup_le (fun g hg d hd => ?_) (fun g hg d hd => hLtU d hd.1 g hg)
      obtain ⟨u, hu, rfl⟩ := hd.2
      exact hLUt u hu g hg
    exact fun x hx => mem_centSub.mp (hle hx)
  have hLU : ∀ l ∈ L, ∀ u ∈ commSub (orbSup T V) L, l u ∈ commSub (orbSup T V) L := by
    intro l hl u hu
    have h := (commSub (orbSup T V) L).mul_mem
      (Subgroup.subset_closure ⟨l, hl, u, hUV hu, rfl⟩ : l u * u⁻¹ ∈ commSub (orbSup T V) L) hu
    rwa [inv_mul_cancel_right] at h
  have : Group.IsPerfect ↥L := n.std.hyp.quasi.1
  exact rk_add_two_lt_of_perfectQ4 n.std.hyp.exp n.Mp_eq n.std.hyp.irr (d36_V_le_U hL38 n) n.triv
    hLU inf_le_left hDfix

end D36Q4

end CFSG.Quasithin
