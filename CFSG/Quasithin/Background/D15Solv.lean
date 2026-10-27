module

public import CFSG.Quasithin.Background.D15Three
public import CFSG.Quasithin.Background.F9Section

public section

namespace CFSG.Quasithin.D15Proof

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_secImg_of_le {U L N : Subgroup G} (hUe : IsElemAbelian 2 U)
    (hNU : N ≤ U) : IsElemAbelian 2 (secImg (Subgroup.normalizer (L : Set G)) L N) := by
  refine isElemAbelian_secImg_normalizer (fun x hx y hy => ?_) (fun x hx => ?_)
  · rw [(B6.isElemAbelian_iff.mp hUe).1 x (hNU hx) y (hNU hy), mul_inv_cancel_right,
      mul_inv_cancel]
    exact L.one_mem
  · rw [hUe.2 x (hNU hx)]
    exact L.one_mem

theorem normal_two_eq_bot {H U L N : Subgroup G} (hUH : U ≤ H) (hstep : IsChiefStep H U L N)
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (L : Set G)) L N)) :
    ∀ Q : Subgroup (MulAut (secImg (Subgroup.normalizer (L : Set G)) L N)),
      Q ≤ autOn (secImg (Subgroup.normalizer (L : Set G)) L H)
        (secImg (Subgroup.normalizer (L : Set G)) L N) →
      (Q.subgroupOf (autOn (secImg (Subgroup.normalizer (L : Set G)) L H)
        (secImg (Subgroup.normalizer (L : Set G)) L N))).Normal →
      IsPGroup 2 Q → Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.normalizer (L : Set G) with hAdef
  set E := secImg A L N with hEdef
  set X := autOn (secImg A L H) E with hXdef
  intro Q hQX hQn hQ2
  let _ : CommGroup E := commGroupOfElemAbelian hE
  have hHA : H ≤ A := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNH : N ≤ H := hstep.1.1.trans hUH
  have hNA : N ≤ A := hNH.trans hHA
  have hLN : L ≤ N := hstep.2.2.1.le
  let ι : N →* E := ((secMk A L).comp (Subgroup.inclusion hNA)).codRestrict E
    (fun x => secMk_mem_secImg (x := Subgroup.inclusion hNA x) x.2)
  have hι : ∀ x : N, ((ι x : E) : SecQuot A L) = secMk A L (Subgroup.inclusion hNA x) :=
    fun _ => rfl
  have hιs : Function.Surjective ι := by
    rintro ⟨y, hy⟩
    obtain ⟨a, haN, rfl⟩ := mem_secImg.mp hy
    exact ⟨⟨a, haN⟩, Subtype.ext rfl⟩
  have hι1 : ∀ x : N, ι x = 1 ↔ (x : G) ∈ L := by
    intro x
    constructor
    · intro h
      have h1 := congrArg Subtype.val h
      rw [hι, OneMemClass.coe_one] at h1
      exact (secMk_eq_one_iff (A := A) (B := L)).mp h1
    · intro h
      apply Subtype.ext
      rw [hι, OneMemClass.coe_one]
      exact (secMk_eq_one_iff (A := A) (B := L)).mpr h
  set F := fixV Q with hFdef
  obtain ⟨x₀, hx₀N, hx₀L⟩ := IsConcreteLE.exists_of_lt hstep.2.2.1
  have hv₀ : ι ⟨x₀, hx₀N⟩ ≠ 1 := fun h => hx₀L ((hι1 _).mp h)
  have hv₀2 : ι ⟨x₀, hx₀N⟩ ^ 2 = 1 := Subtype.ext (hE.2 _ (ι ⟨x₀, hx₀N⟩).2)
  have h2E : 2 ∣ Nat.card E := by
    have := orderOf_eq_prime hv₀2 hv₀
    rw [← this]
    exact orderOf_dvd_natCard _
  have h2F : 2 ∣ Nat.card F := ((card_modEq_card_fixV hQ2).dvd_iff (dvd_refl 2)).mp h2E
  have hFne : F ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h2F
    exact absurd h2F (by norm_num)
  obtain ⟨⟨f, hfF⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
  obtain ⟨n₀, rfl⟩ := hιs f
  set K : Subgroup G := (F.comap ι).map N.subtype with hKdef
  have hKN : K ≤ N := Subgroup.map_subtype_le _
  have hmemK : ∀ n : N, ι n ∈ F → (n : G) ∈ K := fun n hn => ⟨n, hn, rfl⟩
  have hKmem : ∀ n : N, (n : G) ∈ K → ι n ∈ F := by
    rintro n ⟨m, hm, hmn⟩
    have : m = n := Subtype.ext hmn
    rw [← this]
    exact hm
  have hLK : L ≤ K := fun l hl => hmemK ⟨l, hLN hl⟩ (by
    rw [(hι1 ⟨l, hLN hl⟩).mpr hl]
    exact F.one_mem)
  have hn₀L : (n₀ : G) ∉ L := fun h => hf1 (Subtype.ext ((hι1 n₀).mpr h))
  have hKnorm : IsNormalIn H U K := by
    refine ⟨hKN.trans hstep.1.1, fun g hg x hx => ?_⟩
    obtain ⟨n, hn, rfl⟩ := hx
    have hgn : g * (n : G) * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hg) n).mp n.2
    have hgE : secMk A L ⟨g, hHA hg⟩ ∈ Subgroup.normalizer (E : Set (SecQuot A L)) :=
      secMk_mem_normalizer_secImg (hHN hg)
    set ψ : MulAut E := conjAct E ⟨secMk A L ⟨g, hHA hg⟩, hgE⟩ with hψdef
    have hψX : ψ ∈ X :=
      ⟨⟨secMk A L ⟨g, hHA hg⟩, hgE⟩,
        (secMk_mem_secImg (A := A) (B := L) (X := H) (x := ⟨g, hHA hg⟩) hg :), rfl⟩
    have hψι : ψ (ι n) = ι ⟨g * n * g⁻¹, hgn⟩ := by
      apply Subtype.ext
      rw [hψdef, conjAct_apply_coe', hι, hι]
      have e : (Subgroup.inclusion hNA ⟨g * n * g⁻¹, hgn⟩ : A) =
          ⟨g, hHA hg⟩ * Subgroup.inclusion hNA n * ⟨g, hHA hg⟩⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_inv]
    refine hmemK ⟨g * n * g⁻¹, hgn⟩ fun q hq => ?_
    have hconj : ψ⁻¹ * q * ψ ∈ Q := by
      have := hQn.conj_mem ⟨q, hQX hq⟩ hq (⟨ψ, hψX⟩⁻¹ : X)
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have h1 : (ψ⁻¹ * q * ψ) (ι n) = ι n := hn _ hconj
    rw [← hψι]
    calc q (ψ (ι n)) = ψ ((ψ⁻¹ * q * ψ) (ι n)) := by
          simp [MulAut.mul_apply]
      _ = ψ (ι n) := by rw [h1]
  have hKeq : K = N := (hstep.2.2.2 K hKnorm hLK hKN).resolve_left fun h =>
    hn₀L (h ▸ hmemK n₀ hfF)
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro v
  obtain ⟨n, hn⟩ := hιs v
  rw [MulAut.one_apply, ← hn]
  exact hKmem n (hKeq.ge n.2) q hq

omit [Finite G] in
theorem isSolvable_autOn_secImg {H L N : Subgroup G} (hsolv : Group.IsSolvable H)
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Group.IsSolvable (autOn (secImg (Subgroup.normalizer (L : Set G)) L H)
      (secImg (Subgroup.normalizer (L : Set G)) L N)) := by
  set A := Subgroup.normalizer (L : Set G) with hAdef
  have h1 : Group.IsSolvable (H.subgroupOf A) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hHL).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHL).injective
  have h2 : Group.IsSolvable (secImg A L H) :=
    Group.isSolvable_of_surjective ((secMk A L).subgroupMap_surjective (H.subgroupOf A))
  have hSN : secImg A L H ≤ Subgroup.normalizer (secImg A L N : Set (SecQuot A L)) :=
    secImg_le_normalizer_secImg hHN
  have h3 : Group.IsSolvable ((secImg A L H).subgroupOf
      (Subgroup.normalizer (secImg A L N : Set (SecQuot A L)))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hSN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSN).injective
  exact Group.isSolvable_of_surjective ((conjAct (secImg A L N)).subgroupMap_surjective _)

theorem d125_of_isSolvable {G₂ T U : Subgroup G} (hsolv : Group.IsSolvable G₂) (hTG₂ : T ≤ G₂)
    (hUG₂ : U ≤ G₂) (hUe : IsElemAbelian 2 U) : D125 G₂ T U := by
  intro L N hstep _ A hAT hAe _
  have hG₂L : G₂ ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hG₂N : G₂ ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNU : N ≤ U := hstep.1.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hNU.trans hUG₂).trans hG₂L
  have hAG₂ : A ≤ G₂ := hAT.trans hTG₂
  have hE := isElemAbelian_secImg_of_le (L := L) hUe hNU
  let _ : CommGroup (secImg (Subgroup.normalizer (L : Set G)) L N) := commGroupOfElemAbelian hE
  have hsq : ∀ v : secImg (Subgroup.normalizer (L : Set G)) L N, v ^ 2 = 1 := fun v =>
    Subtype.ext (hE.2 v v.2)
  by_contra hlt
  push Not at hlt
  have hnt : ¬ ∀ b ∈ A, ∀ e ∈ N, b * e * b⁻¹ * e⁻¹ ∈ L := by
    intro hall
    have hCA : centralizerMod L A N = A := le_antisymm (centralizerMod_le_left _ _ _)
      fun b hb => ⟨hb, hG₂L (hAG₂ hb), hall b hb⟩
    rw [hCA, Subgroup.relIndex_self] at hlt
    exact absurd hlt (not_lt.mpr (Nat.one_le_iff_ne_zero.mpr (relIndex_ne_zero _ _)))
  exact B1.not_isStrongFFModule hsq (isSolvable_autOn_secImg hsolv hG₂L hG₂N)
    (normal_two_eq_bot hUG₂ hstep hE)
    (isStrongFFModule_autOn_secImg hE hNL hG₂L hG₂N hAG₂ hAe hnt hlt)

end CFSG.Quasithin.D15Proof
