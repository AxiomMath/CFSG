module

public import CFSG.Quasithin.Background.F918N6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement Matrix

section XCore

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

theorem v2d_le_normalizer (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {A : Subgroup (MulAut X)}
    (hA : A ≤ Tb) : Lb ⊔ A ≤ Subgroup.normalizer (Lb : Set (MulAut X)) := by
  refine sup_le Subgroup.le_normalizer fun a ha => ?_
  have := n6_Tb_le_normalizer h (hA ha)
  rwa [hML] at this

theorem v2d_conj_mem (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {A : Subgroup (MulAut X)}
    (hA : A ≤ Tb) {g : MulAut X} (hg : g ∈ Lb ⊔ A) {l : MulAut X} (hl : l ∈ Lb) :
    g * l * g⁻¹ ∈ Lb :=
  (Subgroup.mem_normalizer_iff.mp (v2d_le_normalizer h hML hA hg) l).mp hl

theorem v2d_cent (h : Z35 Mb Tb Lb Vb) {g : MulAut X} (hg : g ∈ Mb ⊔ Tb) (hg2 : g ^ 2 = 1)
    (hcomm : ∀ m ∈ Mb, g * m = m * g) : g = 1 := by
  have hgc : ∀ m ∈ Mb, ∀ w : X, g (m w) = m (g w) := fun m hm w => by
    have := congrArg (fun φ : MulAut X => φ w) (hcomm m hm)
    simpa [MulAut.mul_apply] using this
  have hgg : ∀ w : X, g (g w) = w := fun w => by
    have := congrArg (fun φ : MulAut X => φ w) hg2
    simpa [pow_two, MulAut.mul_apply] using this
  obtain ⟨m₀, hm₀, a₀, ha₀, hga⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer (n6_Tb_le_normalizer h)).1 hg
  have hfix : ∀ a ∈ Tb, ∀ v ∈ Vb.map a.toMonoidHom, g v = v := by
    intro a ha
    have hmap : (Vb.map a.toMonoidHom).map g.toMonoidHom = Vb.map (a₀ * a).toMonoidHom := by
      rw [n6_map_map, hga, mul_assoc, ← n6_map_map]
      exact n6_map_eq_of_mem_stabSub (n6_stab_map h (Tb.mul_mem ha₀ ha) hm₀)
    have heq := n6_eq_of_map h ha (Tb.mul_mem ha₀ ha) hmap fun m hm v _ => hgc m hm v
    have hst : ∀ v ∈ Vb.map a.toMonoidHom, g v ∈ Vb.map a.toMonoidHom := by
      intro v hv
      have : g v ∈ (Vb.map a.toMonoidHom).map g.toMonoidHom := ⟨v, hv, rfl⟩
      rwa [hmap, ← heq] at this
    exact n6_schur h ha hst (fun v _ => hgg v) fun m hm v _ => hgc m hm v
  have hle : orbSup Tb Vb ≤ MonoidHom.eqLocus g.toMonoidHom (MonoidHom.id X) :=
    orbSup_le fun a ha v hv => hfix a ha v hv
  ext w
  have hw : w ∈ orbSup Tb Vb := by
    rw [h.gen]
    trivial
  simpa using hle hw

theorem v2d_commV_top (h : Z35 Mb Tb Lb Vb) : commV Lb = ⊤ := by
  have := n6_commSub_W h (le_refl Tb) Tb.one_mem
  rwa [h.gen, n6_conjAutSub_one, ← commV_eq_commSub] at this

theorem v2d_exists_move (h : Z35 Mb Tb Lb Vb) : ∃ t ∈ Tb, Vb.map t.toMonoidHom ≠ Vb := by
  by_contra hall
  push Not at hall
  have hle : orbSup Tb Vb ≤ Vb := orbSup_le fun t ht => (hall t ht).le
  rw [h.gen] at hle
  exact absurd h.lt (not_lt_of_ge hle)

theorem v2d_irrSec (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {t : MulAut X} (ht : t ∈ Tb) :
    ⊥ ≤ Vb.map t.toMonoidHom ∧ Vb.map t.toMonoidHom ≤ ⊤ ∧
      XMod.IsInv ↥Lb (Vb.map t.toMonoidHom) ∧ XMod.IsIrrSec ↥Lb ⊥ (Vb.map t.toMonoidHom) := by
  subst hML
  refine ⟨bot_le, le_top, fun k w hw => n6_inv_map h ht k.2 hw, bot_lt_iff_ne_bot.2 fun h0 => ?_,
    fun J hJ _ hJS => ?_⟩
  · exact h.irr.2.1.ne' ((Subgroup.map_eq_bot_iff_of_injective _ t.injective).1 h0)
  · exact n6_irr_map h ht hJS fun m hm u hu => hJ ⟨m, hm⟩ u hu

theorem v2d_eq_of_secIsoL (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {t t' : MulAut X}
    (ht : t ∈ Tb) (ht' : t' ∈ Tb)
    (hiso : SecIsoL Lb (Vb.map t.toMonoidHom) ⊥ (Vb.map t'.toMonoidHom) ⊥) :
    Vb.map t.toMonoidHom = Vb.map t'.toMonoidHom := by
  subst hML
  obtain ⟨e, he⟩ := InternalSec.equiv_of_secIsoL hiso
  refine h.homog t ht t' ht' ⟨e, fun m l l' hl => ?_⟩
  have hw : (m : MulAut X) (l : X) ∈ Vb.map t.toMonoidHom := n6_inv_map h ht m.2 l.2
  have hw' : (m : MulAut X) ((e l : ↥(Vb.map t'.toMonoidHom)) : X) ∈ Vb.map t'.toMonoidHom :=
    n6_inv_map h ht' m.2 (e l).2
  have hkey := he m l hw hw'
  have hl' : (⟨(m : MulAut X) (l : X), hw⟩ : ↥(Vb.map t.toMonoidHom)) = l' := Subtype.ext hl
  rw [hl'] at hkey
  change (m : MulAut X) ((e l : ↥(Vb.map t'.toMonoidHom)) : X) =
    ((e l' : ↥(Vb.map t'.toMonoidHom)) : X)
  rw [hkey]

theorem v2d_sqtk (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) (hA21 : AsA21SQTKSection) :
    SQTKGroup ↥Lb := by
  obtain ⟨S, _, _, hSQ, hSK, φ, hφ⟩ := h.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQ p hp hp2, hSK⟩
  have hLMT : Lb ≤ Mb ⊔ Tb := by
    rw [hML]
    exact le_sup_left
  let H : Subgroup S := (Lb.subgroupOf (Mb ⊔ Tb)).comap φ
  let ψ : ↥H →* ↥Lb :=
    { toFun := fun x => ⟨((φ x : ↥(Mb ⊔ Tb)) : MulAut X), x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hψ : Function.Surjective ψ := by
    rintro ⟨g, hg⟩
    obtain ⟨y, hy⟩ := hφ ⟨g, hLMT hg⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show φ y ∈ Lb.subgroupOf (Mb ⊔ Tb)
      rw [hy]
      exact hg
    · apply Subtype.ext
      show ((φ y : ↥(Mb ⊔ Tb)) : MulAut X) = g
      simp [hy]
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥Lb) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h.quasi
  refine hA21 S hS H _ ψ hψ ⊤ (B5.layer_eq_top_of_quasisimple hq') fun g => ⟨0, ?_⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  rw [pow_zero, pow_one, QuotientGroup.eq_one_iff]
  trivial

theorem x_core_sumNatDual {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)}
    {Vb : Subgroup X} (hB56 : AsB56) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {A : Subgroup (MulAut X)} (hAT : A ≤ Tb)
    (hAe : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hr : Nat.card X ≤ Nat.card A * Nat.card ↥(fixV A)) :
    ∃ n, SumNatDual Lb (⊤ : Subgroup X) n := by
  have hLMT : Lb ≤ Mb ⊔ Tb := by
    rw [hML]
    exact le_sup_left
  have hGMT : Lb ⊔ A ≤ Mb ⊔ Tb := sup_le hLMT (hAT.trans le_sup_right)
  have hKn : ∀ m ∈ Lb, ∀ k ∈ Lb, m * k * m⁻¹ ∈ Lb := fun m hm k hk =>
    Lb.mul_mem (Lb.mul_mem hm hk) (Lb.inv_mem hm)
  have hMn : ∀ j ∈ Lb ⊔ A, ∀ m ∈ Lb, j * m * j⁻¹ ∈ Lb := fun j hj m hm =>
    v2d_conj_mem h hML hAT hj hm
  have hA2 : IsA2 (Lb ⊔ A) A := ⟨le_sup_right, hAne, hAe⟩
  obtain ⟨B, hBA, hB, -⟩ := B1.exists_offender_below hA2 0 (by rw [add_zero]; exact hr)
  set G := Lb ⊔ A with hG
  set J := ffJ G with hJdef
  have hLG : Lb ≤ G := le_sup_left
  have hJG : J ≤ G := B6.ffJ_le G
  have hJn : ∀ g ∈ G, ∀ j ∈ J, g * j * g⁻¹ ∈ J := fun g hg j hj =>
    (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ G hg) j).mp hj
  have hBJ : B ≤ J := B6.le_ffJ hB
  have hQ : pCoreOf 2 G = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
    have hQG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
    have hQn : ∀ g ∈ G, ∀ q ∈ pCoreOf 2 G, g * q * g⁻¹ ∈ pCoreOf 2 G :=
      fun g hg q hq => B1Red.conj_mem_pCoreOf hg hq
    have hLQ : Lb ≤ Subgroup.centralizer (pCoreOf 2 G : Set (MulAut X)) := by
      intro k hk
      rcases n6_le_or_commute h.quasi le_rfl hLG hKn hMn hQG hQn with hle | hc
      · exfalso
        have : Group.IsPerfect ↥Lb := h.quasi.1
        have : Nontrivial ↥Lb := CFSG.LocalCores.isQuasisimple_nontrivial h.quasi
        exact Group.IsPerfect.not_isNilpotent _ (hQ2.to_le hle).isNilpotent
      · exact Subgroup.mem_centralizer_iff.2 fun q hq => (hc k hk q hq).symm
    by_contra hne
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.1 (by simpa using hn))
    have h2 : 2 ∣ Nat.card ↥(pCoreOf 2 G) := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hqd : orderOf q ∣ 2 := by simp [hq]
    have hq2 : (q : MulAut X) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, orderOf_dvd_iff_pow_eq_one.1 hqd, Subgroup.coe_one]
    have hq1 := v2d_cent h (hGMT (hQG q.2)) hq2 fun m hm =>
      Subgroup.mem_centralizer_iff.1 (hLQ (hML ▸ hm)) q q.2
    have : q = 1 := Subtype.ext hq1
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)
  have hLJ : Lb ≤ J := by
    rcases n6_le_or_commute h.quasi le_rfl hLG hKn hMn hJG hJn with hle | hc
    · exact hle
    · exfalso
      obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB.2.1
      apply hb1
      apply Subtype.ext
      exact v2d_cent h (hGMT (Subgroup.mem_sup_right (hBA b.2))) (hB.2.2.1.2 b b.2)
        fun m hm => (hc m (hML ▸ hm) b (hBJ b.2)).symm
  have hQJ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J G hJG
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJG).2 (B6.le_normalizer_ffJ G))
    rw [hQ] at this
    exact le_bot_iff.1 this
  have hJsqtk : IsQuotientOfSQTKTC ↥J :=
    n6_isQuotientOfSQTK_of_le (hJG.trans hGMT) h.qsqtk
  have hb53 : B53Hyp J := ⟨hQJ, (InternalSec.ffJ_ffJ _).symm, n6_b53_clause hJsqtk⟩
  have hJne : J ≠ ⊥ := fun hJ0 => hB.2.1 (eq_bot_iff.2 (hJ0 ▸ hBJ))
  have hcases := hB56 X h.exp J hJne hb53
  have hcomm := v2d_commV_top h
  have hF : quasithinGenFitting J = Lb :=
    n6_genFitting_eq_of_b56Cases h.quasi le_rfl hLJ hKn
      (fun j hj m hm => hMn j (hJG hj) m hm) hcomm hcases
  have hZ : centerOf J ≤ Lb := hF ▸ InternalSec.centerOf_le_quasithinGenFitting J
  have hb51 : B51Hyp J Lb := by
    refine ⟨?_, h.quasi, v2d_sqtk h hML hA21, hLJ, hQJ, (InternalSec.ffJ_ffJ _).symm⟩
    rw [hF, sup_eq_left.2 hZ]
  have hfix : fixV Lb = ⊥ := by rw [← hML]; exact h.fix
  have h3 := (hB51 X h.exp J Lb hb51).2.2.1
  unfold B51Part3 at h3
  rw [hcomm, hfix, bot_inf_eq] at h3
  rcases h3 with hhom | hsum
  · exfalso
    obtain ⟨t, ht, htV⟩ := v2d_exists_move h
    have hiso := hhom.2 _ _ (v2d_irrSec h hML (Tb.one_mem)) (v2d_irrSec h hML ht)
    exact htV ((v2d_eq_of_secIsoL h hML Tb.one_mem ht hiso).symm.trans (n6_map_one Vb))
  · exact hsum

end XCore

end CFSG.Quasithin
