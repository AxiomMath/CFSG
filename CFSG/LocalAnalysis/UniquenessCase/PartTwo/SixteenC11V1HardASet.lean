module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardRes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigModelBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

private theorem s16c11_v1_rkIdx_prod_self {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) : rkIdx (S.prod S) = 2 * rkIdx S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rkIdx
  rw [Subgroup.index_prod]
  rw [padicValNat.mul (Subgroup.index_ne_zero_of_finite (H := S))
    (Subgroup.index_ne_zero_of_finite (H := S))]
  ring

private theorem s16c11_v1_rkIdx_map_equiv {G N : Type*} [Group G] [Group N]
    (e : G ≃* N) (S : Subgroup G) : rkIdx (S.map (e : G →* N)) = rkIdx S := by
  unfold rkIdx
  rw [Subgroup.index_map_equiv]

private theorem s16c11_v1_fixV_prod_map {W : Type} [CommGroup W] {J₀ : Subgroup W}
    {L : Subgroup (MulAut W)} (φ : ↥L →* MulAut ↥J₀) (Θ : ↥J₀ × ↥J₀ ≃* W)
    (hΘ : ∀ (l : ↥L) (p : ↥J₀ × ↥J₀), (l : MulAut W) (Θ p) = Θ (φ l p.1, φ l p.2))
    (B : Subgroup (MulAut W)) (hB : B ≤ L) :
    fixV B = ((fixV ((B.subgroupOf L).map φ)).prod
      (fixV ((B.subgroupOf L).map φ))).map (Θ : ↥J₀ × ↥J₀ →* W) := by
  ext w
  constructor
  · intro hw
    have hcoord : ∀ b : MulAut ↥J₀, b ∈ (B.subgroupOf L).map φ →
        b (Θ.symm w).1 = (Θ.symm w).1 ∧ b (Θ.symm w).2 = (Θ.symm w).2 := by
      intro b hb
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hb
      have hfix := mem_fixV.mp hw (l : MulAut W) (Subgroup.mem_subgroupOf.mp hl)
      have hp : Θ.symm w = (φ l (Θ.symm w).1, φ l (Θ.symm w).2) := by
        apply Θ.injective
        rw [MulEquiv.apply_symm_apply, ← hΘ l (Θ.symm w), MulEquiv.apply_symm_apply, hfix]
      exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
    refine Subgroup.mem_map.mpr ⟨Θ.symm w, Subgroup.mem_prod.mpr ⟨?_, ?_⟩,
      Θ.apply_symm_apply w⟩
    · exact mem_fixV.mpr fun b hb => (hcoord b hb).1
    · exact mem_fixV.mpr fun b hb => (hcoord b hb).2
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hw
    refine mem_fixV.mpr ?_
    intro b hb
    have hp1 : p.1 ∈ fixV ((B.subgroupOf L).map φ) := (Subgroup.mem_prod.mp hp).1
    have hp2 : p.2 ∈ fixV ((B.subgroupOf L).map φ) := (Subgroup.mem_prod.mp hp).2
    have hmem : φ ⟨b, hB hb⟩ ∈ (B.subgroupOf L).map φ :=
      Subgroup.mem_map.mpr ⟨⟨b, hB hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have h1 : φ ⟨b, hB hb⟩ p.1 = p.1 := mem_fixV.mp hp1 _ hmem
    have h2 : φ ⟨b, hB hb⟩ p.2 = p.2 := mem_fixV.mp hp2 _ hmem
    change ((⟨b, hB hb⟩ : ↥L) : MulAut W) (Θ p) = Θ p
    rw [hΘ ⟨b, hB hb⟩ p, h1, h2]

theorem s16c11_v1_aSet_cover {W : Type} [CommGroup W] [Finite W] {X K L : Subgroup (MulAut W)}
    {J₀ : Subgroup W} (hM : S16C11Model X K J₀) (hLX : L ≤ X)
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) (hJ : ∀ l ∈ L, ∀ j ∈ J₀, l j ∈ J₀)
    {E : Subgroup (MulAut W)} (hEL : E ≤ L) (hE : E ∈ E3.aSet 2 X) :
    (E.subgroupOf L).map (CFSG.Quasithin.H13.VolI.resHom L J₀ hJ) ∈
        E3.aSet 2 (CFSG.Quasithin.H13.VolI.resHom L J₀ hJ).range ∧
      rkIdx (fixV E) =
        2 * rkIdx (fixV ((E.subgroupOf L).map (CFSG.Quasithin.H13.VolI.resHom L J₀ hJ))) := by
  classical
  obtain ⟨hJ', Θ, hΘ⟩ := s16c11_v1_model_pair hM hLX hLK
  have hJeq : hJ = hJ' := Subsingleton.elim _ _
  rw [hJeq]
  let φ : ↥L →* MulAut ↥J₀ := CFSG.Quasithin.H13.VolI.resHom L J₀ hJ'
  have hinj : Function.Injective φ := s16c11_v1_resHom_injective hM hLX hLK hJ'
  let Ē : Subgroup (MulAut ↥J₀) := (E.subgroupOf L).map φ
  have hĒle : Ē ≤ φ.range := Subgroup.map_le_range φ (E.subgroupOf L)
  have hĒne : Ē ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff] at hbot
    have hker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr hinj
    rw [hker] at hbot
    apply hE.2.1
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : (⟨x, hEL hx⟩ : ↥L) ∈ E.subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
    have h1 : (⟨x, hEL hx⟩ : ↥L) = 1 := by
      have := hbot hx'
      simpa using this
    exact congrArg Subtype.val h1
  have hĒab : IsElemAbelian2 Ē := by
    constructor
    · intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      calc φ a' * φ b' = φ (a' * b') := (map_mul φ a' b').symm
        _ = φ (b' * a') := congrArg φ (Subtype.ext (hE.2.2.1.1 _
              (Subgroup.mem_subgroupOf.mp ha') _ (Subgroup.mem_subgroupOf.mp hb')))
        _ = φ b' * φ a' := map_mul φ b' a'
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      rw [← map_pow, show a' ^ 2 = 1 from
        Subtype.ext (hE.2.2.1.2 _ (Subgroup.mem_subgroupOf.mp ha')), map_one]
  have hĒfix : ∀ Bbar : Subgroup (MulAut ↥J₀), Bbar ≤ Ē → E3.mQuot Ē Bbar < 2 →
      fixV Bbar = fixV Ē := by
    intro Bbar hBbar hmq
    let B : Subgroup (MulAut W) := (Bbar.comap φ).map L.subtype
    have hBL : B ≤ L := by
      intro x hx
      obtain ⟨l, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact l.2
    have hBbareq : (B.subgroupOf L).map φ = Bbar := by
      have h1 : B.subgroupOf L = Bbar.comap φ := by
        show ((Bbar.comap φ).map L.subtype).comap L.subtype = Bbar.comap φ
        rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
      rw [h1]
      exact Subgroup.map_comap_eq_self (hBbar.trans hĒle)
    have hBleE : B ≤ E := by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      have hφl : φ l ∈ Bbar := Subgroup.mem_comap.mp hl
      have hφlE : φ l ∈ Ē := hBbar hφl
      obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hφlE
      have hel : e = l := hinj heq
      rw [← hel]
      exact Subgroup.mem_subgroupOf.mp he
    have hrel : B.relIndex E = Bbar.relIndex Ē := by
      rw [← Subgroup.relIndex_subgroupOf hEL, ← hBbareq]
      exact (Subgroup.relIndex_map_map_of_injective (B.subgroupOf L) (E.subgroupOf L)
        hinj).symm
    have hmqE : E3.mQuot E B < 2 := by
      change padicValNat 2 (B.relIndex E) < 2
      rw [hrel]
      exact hmq
    have hfix := hE.2.2.2 B hBleE hmqE
    have hfixB : fixV B = ((fixV Bbar).prod (fixV Bbar)).map (Θ : ↥J₀ × ↥J₀ →* W) := by
      rw [s16c11_v1_fixV_prod_map φ Θ hΘ B hBL, hBbareq]
    have hfixE : fixV E = ((fixV Ē).prod (fixV Ē)).map (Θ : ↥J₀ × ↥J₀ →* W) :=
      s16c11_v1_fixV_prod_map φ Θ hΘ E hEL
    have hmap : ((fixV Bbar).prod (fixV Bbar)).map (Θ : ↥J₀ × ↥J₀ →* W) =
        ((fixV Ē).prod (fixV Ē)).map (Θ : ↥J₀ × ↥J₀ →* W) := by
      rw [← hfixB, ← hfixE]
      exact hfix
    have hprod : (fixV Bbar).prod (fixV Bbar) = (fixV Ē).prod (fixV Ē) :=
      Subgroup.map_injective Θ.injective hmap
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      have hmem : (x, 1) ∈ (fixV Bbar).prod (fixV Bbar) := by
        rw [Subgroup.mem_prod]; exact ⟨hx, Subgroup.one_mem _⟩
      rw [hprod] at hmem
      exact (Subgroup.mem_prod.mp hmem).1
    · intro hx
      have hmem : (x, 1) ∈ (fixV Ē).prod (fixV Ē) := by
        rw [Subgroup.mem_prod]; exact ⟨hx, Subgroup.one_mem _⟩
      rw [← hprod] at hmem
      exact (Subgroup.mem_prod.mp hmem).1
  have hmem : Ē ∈ E3.aSet 2 φ.range := ⟨hĒle, hĒne, hĒab, hĒfix⟩
  have hrk : rkIdx (fixV E) = 2 * rkIdx (fixV Ē) := by
    have hfixE := s16c11_v1_fixV_prod_map φ Θ hΘ E hEL
    rw [hfixE, s16c11_v1_rkIdx_map_equiv Θ ((fixV Ē).prod (fixV Ē)),
      s16c11_v1_rkIdx_prod_self (fixV Ē)]
  exact ⟨hmem, hrk⟩

theorem s16c11_v1_aSet_le_right {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X K L₀ : Subgroup (MulAut W)} (hK : IsSym ↥K 3) (hdir : IsInternalDirect K L₀ X)
    {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet 2 X) : E ≤ L₀ := by
  classical
  obtain ⟨s⟩ := hK
  let Y : Subgroup (MulAut W) :=
    ((alternatingGroup (Fin 3)).comap s.toMonoidHom).map K.subtype
  have hYcard : Nat.card Y = 3 := s16c11_big_modelb_three_card s
  have hYodd : ¬ 2 ∣ Nat.card Y := by rw [hYcard]; norm_num
  have hYleK : Y ≤ K := Subgroup.map_subtype_le _
  have hKnorm : K ≤ Subgroup.normalizer (Y : Set (MulAut W)) :=
    s16c11_big_modelb_map_subtype_normalizer K _ (alternatingGroup.normal.comap s.toMonoidHom)
  have hcommKL : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k := s16c11_comm_of_isInternalDirect hdir
  have hLcent : L₀ ≤ Subgroup.centralizer (Y : Set (MulAut W)) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcommKL y (hYleK hy) l hl
  have hsup : X ≤ Subgroup.normalizer (Y : Set (MulAut W)) := by
    rw [← hdir.2.2]
    exact sup_le hKnorm (hLcent.trans (Subgroup.centralizer_le_normalizer _))
  have hEnorm : E ≤ Subgroup.normalizer (Y : Set (MulAut W)) := hE.1.trans hsup
  have hEcent : E ≤ Subgroup.centralizer (Y : Set (MulAut W)) :=
    s16c11_le_centralizer_of_mem_aSet_two hW hE hYodd hEnorm
  intro x hx
  have hxX : x ∈ K ⊔ L₀ := by rw [hdir.2.2]; exact hE.1 hx
  obtain ⟨κ, hκ, ℓ, hℓ, hκℓ⟩ := s16c2m_exists_mul_of_mem_sup hcommKL hxX
  have hx2 : x ^ 2 = 1 := hE.2.2.1.2 x hx
  have hκℓcomm : Commute κ ℓ := hcommKL κ hκ ℓ hℓ
  have hxcent : x ∈ Subgroup.centralizer (Y : Set (MulAut W)) := hEcent hx
  have hℓcent : ℓ ∈ Subgroup.centralizer (Y : Set (MulAut W)) := hLcent hℓ
  have hκcent : κ ∈ Subgroup.centralizer (Y : Set (MulAut W)) := by
    have h1 : x * ℓ⁻¹ ∈ Subgroup.centralizer (Y : Set (MulAut W)) :=
      (Subgroup.centralizer (Y : Set (MulAut W))).mul_mem hxcent
        ((Subgroup.centralizer (Y : Set (MulAut W))).inv_mem hℓcent)
    rw [← hκℓ, mul_inv_cancel_right] at h1
    exact h1
  have hκY : κ ∈ Y := s16c11_big_modelb_three_mem_of_centralizer s hκ hκcent
  have hκ3 : κ ^ 3 = 1 := s16c11_big_modelb_three_pow_three s hκ hκY
  have hκ2 : κ ^ 2 = 1 := by
    have h1 : κ ^ 2 * ℓ ^ 2 = 1 := by
      rw [← hκℓcomm.mul_pow 2, hκℓ, hx2]
    have h2 : κ ^ 2 = (ℓ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmemL : κ ^ 2 ∈ L₀ := by
      rw [h2]
      exact L₀.inv_mem (L₀.pow_mem hℓ 2)
    have hmem : κ ^ 2 ∈ K ⊓ L₀ := ⟨K.pow_mem hκ 2, hmemL⟩
    rwa [hdir.2.1, Subgroup.mem_bot] at hmem
  have hκ1 : κ = 1 := by
    calc κ = κ ^ 3 * (κ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hκ3, hκ2]; simp
  rw [← hκℓ, hκ1, one_mul]
  exact hℓ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
