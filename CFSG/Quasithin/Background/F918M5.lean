module

public import CFSG.Quasithin.Background.F918H0
public import CFSG.Quasithin.Background.PGroupIrrTrivial
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem le_normalizer_of_forall_conj_mem_m5 {H N : Subgroup (MulAut W)}
    (h : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : H ≤ Subgroup.normalizer (N : Set (MulAut W)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h g hg n, fun hn => ?_⟩
  have h1 := h g⁻¹ (H.inv_mem hg) _ hn
  have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [e] at h1

omit [Finite W] in
private theorem D31.Mp_le_M_m5 {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) : Mp ≤ M := by
  rw [hD.Mp_eq]
  exact conjClosure_le fun s hs l hl =>
    M.mul_mem (M.mul_mem (hD.sylow.1 hs) (le_of_mem_cComp hD.comp hl)) (M.inv_mem (hD.sylow.1 hs))

omit [Finite W] in
private theorem D31.Mp_le_stabSub_orbSup {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) : Mp ≤ stabSub (orbSup T V) := by
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    rw [hD.Mp_eq]; exact le_normalizer_conjClosure L T
  have hinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := (mem_irrPlus_top_iff.mp hD.irr).1
  have key : ∀ x ∈ Mp, ∀ u ∈ orbSup T V, x u ∈ orbSup T V := by
    intro x hx u hu
    have hle : orbSup T V ≤ (orbSup T V).comap x.toMonoidHom := by
      refine orbSup_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      have hx' : s⁻¹ * x * s ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hTn hs) x).mp hx
      show x (s v) ∈ orbSup T V
      have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
      rw [h1]
      exact map_le_orbSup hs ⟨_, hinv _ hx' v hv, rfl⟩
    exact hle hu
  intro x hx u
  refine ⟨fun h => ?_, fun h => key x hx u h⟩
  have := key x⁻¹ (Mp.inv_mem hx) _ h
  simpa using this

omit [Finite W] in
private theorem D31.exists_ne_orbSup {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) : ∃ l ∈ L, ∃ w ∈ orbSup T V, l w ≠ w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp hD.irr
  have hMp : Mp ≤ centSub (orbSup T V) := by
    rw [hD.Mp_eq]
    refine conjClosure_le fun s hs l hl => ?_
    intro w hw
    have h1 : l (s⁻¹ w) = s⁻¹ w := hcon l hl _ (mem_orbSup_of_mem_map (T.inv_mem hs) hw)
    show s (l (s⁻¹ w)) = w
    rw [h1]
    simp
  apply hlt.not_ge
  intro v hv
  exact ⟨hv, fun m hm => hMp hm v (le_orbSup T V hv)⟩

private theorem pCoreOf_autSub_orbSup_eq_bot_aux {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) (hnt : ∃ l ∈ L, ∃ w ∈ orbSup T V, l w ≠ w) :
    pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hD.sylow.1
  have hLMp : L ≤ Mp := by rw [hD.Mp_eq]; exact le_conjClosure L T
  have hTX : T ≤ Mp ⊔ T := le_sup_right
  have hLX : L ≤ Mp ⊔ T := hLMp.trans le_sup_left
  have hXM : Mp ⊔ T ≤ M := sup_le hD.Mp_le_M_m5 hTM
  have hXs : Mp ⊔ T ≤ stabSub (orbSup T V) :=
    sup_le hD.Mp_le_stabSub_orbSup (le_stabSub_orbSup T V)
  let ρ : ↥(Mp ⊔ T) →* MulAut ↥(orbSup T V) := (resHom (orbSup T V)).comp (Subgroup.inclusion hXs)
  have hrange : autSub (Mp ⊔ T) (orbSup T V) = ρ.range := by
    ext φ
    rw [mem_autSub, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hXs x.2⟩, x.2, rfl⟩
  have hY2 : IsPGroup 2 (pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hYn : autSub (Mp ⊔ T) (orbSup T V) ≤
      Subgroup.normalizer (pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) : Set (MulAut ↥(orbSup T V))) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  let Yt : Subgroup ↥(Mp ⊔ T) := (pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V))).comap ρ
  have hYtn : Yt.Normal := by
    refine ⟨fun y hy g => ?_⟩
    have hg : ρ g ∈ autSub (Mp ⊔ T) (orbSup T V) := by rw [hrange]; exact ⟨g, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hYn hg) _).mp hy
  have hLc : L ∈ cComp (Mp ⊔ T) := cComp_mem_of_le hD.comp hLX hXM
  have hcomp : CFSG.IsComponent (L.subgroupOf (Mp ⊔ T)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX).symm hD.quasi,
      A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (subgroupOf_mem_cComp hLc))⟩
  have hLY : ∀ l ∈ L, ∀ y : ↥(Mp ⊔ T), y ∈ Yt → l * (y : MulAut W) = y * l := by
    rcases CFSG.LocalCores.component_normal_subgroup hcomp hYtn with h | h
    · exfalso
      obtain ⟨l, hl, w, hw, hne⟩ := hnt
      have hLstY : (L.subgroupOf (Mp ⊔ T)).map ρ ≤ pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) :=
        Subgroup.map_le_iff_le_comap.mpr h
      have hperf : ⁅(L.subgroupOf (Mp ⊔ T)).map ρ, (L.subgroupOf (Mp ⊔ T)).map ρ⁆ =
          (L.subgroupOf (Mp ⊔ T)).map ρ := by
        rw [← Subgroup.map_commutator, perfect_of_mem_cComp (subgroupOf_mem_cComp hLc)]
      have hne' : (L.subgroupOf (Mp ⊔ T)).map ρ ≠ ⊥ := by
        intro hbot
        have h1 : ρ ⟨l, hLX hl⟩ ∈ (L.subgroupOf (Mp ⊔ T)).map ρ := ⟨⟨l, hLX hl⟩, hl, rfl⟩
        rw [hbot, Subgroup.mem_bot] at h1
        exact hne (congrArg (fun φ : MulAut ↥(orbSup T V) => ((φ ⟨w, hw⟩ : ↥(orbSup T V)) : W)) h1)
      have : Group.IsPerfect ↥((L.subgroupOf (Mp ⊔ T)).map ρ) := Subgroup.isPerfect_iff.mpr hperf
      have : Nontrivial ↥((L.subgroupOf (Mp ⊔ T)).map ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne'
      exact Group.IsPerfect.not_isNilpotent _ (hY2.to_le hLstY).isNilpotent
    · intro l hl y hy
      have hc := Subgroup.commutator_mem_commutator
        (show (⟨l, hLX hl⟩ : ↥(Mp ⊔ T)) ∈ L.subgroupOf (Mp ⊔ T) from hl) hy
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact congrArg Subtype.val hc
  have hMpY : ∀ m ∈ Mp, ∀ y : ↥(Mp ⊔ T), y ∈ Yt → (y : MulAut W) * m = m * y := by
    have hle : Mp ≤ Subgroup.centralizer ((Yt.map (Mp ⊔ T).subtype : Subgroup (MulAut W)) :
        Set (MulAut W)) := by
      refine hD.Mp_eq.le.trans (conjClosure_le fun s hs l hl => ?_)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (⟨s, hTX hs⟩⁻¹ * y * ⟨s, hTX hs⟩ : ↥(Mp ⊔ T)) ∈ Yt := by
        have := hYtn.conj_mem y hy ⟨s, hTX hs⟩⁻¹
        simpa using this
      have hc := hLY l hl _ hy'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
      show (y : MulAut W) * (s * l * s⁻¹) = s * l * s⁻¹ * y
      calc (y : MulAut W) * (s * l * s⁻¹) = s * ((s⁻¹ * y * s) * l) * s⁻¹ := by group
        _ = s * (l * (s⁻¹ * y * s)) * s⁻¹ := by rw [hc]
        _ = s * l * s⁻¹ * y := by group
    intro m hm y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hm)) y ⟨y, hy, rfl⟩
  let P : Subgroup (MulAut W) := Yt.map (Mp ⊔ T).subtype ⊓ T
  have hPT : P ≤ T := inf_le_right
  have hPX : P ≤ Mp ⊔ T := hPT.trans hTX
  have hP2 : IsPGroup 2 P := hD.sylow.2.1.to_le hPT
  have hPMp : ∀ p ∈ P, ∀ m ∈ Mp, p * m = m * p := by
    rintro _ ⟨⟨y, hy, rfl⟩, -⟩ m hm
    exact hMpY m hm y hy
  have hPn : Mp ⊔ T ≤ Subgroup.normalizer (P : Set (MulAut W)) := by
    refine sup_le ?_ ?_
    · refine le_normalizer_of_forall_conj_mem_m5 fun m hm p hp => ?_
      rw [← hPMp p hp m hm, mul_inv_cancel_right]
      exact hp
    · refine le_normalizer_of_forall_conj_mem_m5 fun s hs p hp => ?_
      obtain ⟨hp1, hp2⟩ := Subgroup.mem_inf.mp hp
      obtain ⟨y, hy, hyp⟩ := Subgroup.mem_map.mp hp1
      have h1 : (⟨s, hTX hs⟩ * y * ⟨s, hTX hs⟩⁻¹ : ↥(Mp ⊔ T)) ∈ Yt := hYtn.conj_mem y hy _
      have h2 : (Mp ⊔ T).subtype (⟨s, hTX hs⟩ * y * ⟨s, hTX hs⟩⁻¹) = s * p * s⁻¹ := by
        rw [← hyp]
        rfl
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨_, h1, h2⟩,
        T.mul_mem (T.mul_mem hs hp2) (T.inv_mem hs)⟩
  have hPO : P ≤ pCoreOf 2 (Mp ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPX hPn hP2
  have hP1 : ∀ p ∈ P, ∀ v ∈ V, p v = v :=
    trivial_on_of_isPGroup_commute hD.exp hD.irr hP2 (fun p hp v hv => hD.o2inv p (hPO hp) v hv)
      hPMp
  have hPT1 : ∀ p ∈ P, ∀ w ∈ orbSup T V, p w = w := by
    intro p hp w hw
    have hgen : orbSup T V ≤ (p : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
      refine orbSup_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      have hconj : s⁻¹ * p * s ∈ P := (Subgroup.mem_normalizer_iff''.mp (hPn (hTX hs)) p).mp hp
      have h1 := hP1 _ hconj v hv
      simp only [MulAut.mul_apply] at h1
      show p (s v) = s v
      calc p (s v) = s (s⁻¹ (p (s v))) := by simp
        _ = s v := by rw [h1]
    exact hgen hw
  have hodd : ¬ 2 ∣ (T.subgroupOf (Mp ⊔ T)).index := fun h => hD.sylow.2.2 (by
    have e := Subgroup.relIndex_mul_relIndex T (Mp ⊔ T) M hTX hXM
    have h' : 2 ∣ T.relIndex M := e ▸ h.mul_right _
    exact h')
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hQ2 : IsPGroup 2 ((T.subgroupOf (Mp ⊔ T)).map ρ.rangeRestrict) :=
    (hD.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm).map ρ.rangeRestrict
  have hQi : ¬ 2 ∣ ((T.subgroupOf (Mp ⊔ T)).map ρ.rangeRestrict).index := fun h =>
    hodd (h.trans (Subgroup.index_map_dvd _ hsurj))
  have hNn : (Yt.map ρ.rangeRestrict).Normal := hYtn.map ρ.rangeRestrict hsurj
  have hN2 : IsPGroup 2 (Yt.map ρ.rangeRestrict) :=
    (hY2.comap_of_injective ρ.range.subtype ρ.range.subtype_injective).to_le (by
      rintro _ ⟨x, hx, rfl⟩
      exact hx)
  have hNQ : Yt.map ρ.rangeRestrict ≤ (hQ2.toSylow hQi : Subgroup ↥ρ.range) :=
    hN2.le_sylow_of_normal (hQ2.toSylow hQi)
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  have hφG : φ ∈ ρ.range := hrange ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 _ hφ
  obtain ⟨x, rfl⟩ := hφG
  have hx : x ∈ Yt := hφ
  have hmem : ρ.rangeRestrict x ∈ (T.subgroupOf (Mp ⊔ T)).map ρ.rangeRestrict := hNQ ⟨x, hx, rfl⟩
  obtain ⟨s, hsT, hsx⟩ := hmem
  have hsx' : ρ s = ρ x := congrArg Subtype.val hsx
  have hsY : s ∈ Yt := by
    show ρ s ∈ pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V))
    rw [hsx']
    exact hφ
  have hsP : (s : MulAut W) ∈ P := ⟨⟨s, hsY, rfl⟩, hsT⟩
  rw [← hsx']
  ext u
  exact hPT1 _ hsP u u.2

theorem D31.pCoreOf_autSub_orbSup_eq_bot {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) : pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) = ⊥ :=
  pCoreOf_autSub_orbSup_eq_bot_aux hD hD.exists_ne_orbSup

section D36

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}

private theorem d36_exists_ne_m5 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
  obtain ⟨-, hc, -, -⟩ := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  have hn : conjAutSub t L ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      ((Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hx)) y hy).symm)
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp n.std.hyp.irr
  apply hlt.not_ge
  intro v hv
  refine ⟨hv, fun a ha => ?_⟩
  have ha' : a ∈ ((L ⊔ conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [← n.Mp_eq]
    exact ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L (conjAutSub t L) hn] at ha'
  obtain ⟨l, hl, l', hl', rfl⟩ := ha'
  show l (l' v) = v
  rw [n.triv v hv l' hl', hcon l hl v hv]

theorem d36_pCoreOf_eq_bot (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) = ⊥ := by
  obtain ⟨l, hl, v, hv, hne⟩ := d36_exists_ne_m5 hL38 n
  exact pCoreOf_autSub_orbSup_eq_bot_aux n.std.hyp ⟨l, hl, v, le_orbSup T V hv, hne⟩

end D36

end CFSG.Quasithin
