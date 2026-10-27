module

public import CFSG.Quasithin.H13.A5V1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

theorem swapL21367_of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h56 : AsB56) : SwapL21367 := by
  intro G _ _ T L V S hH K hK hgood t ht hne G₁ G₂ hsup hinf hc hK₁ hK₂ n F _ _ hn hF he
  obtain ⟨e⟩ := he
  have hF' := hH.hF
  have hUe := S.elemAbelian_Uv h1222 h517 hF'
  have : IsMulCommutative ↥S.Uv := hUe.1
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
  have hGU := S.Gv_le_normalizer_Uv
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := le_of_mem_cComp hK
  have hKU : K ≤ Subgroup.normalizer (S.Uv : Set G) := hKG.trans hGU
  have htG : t ∈ Subgroup.centralizer ({S.v12} : Set G) := S.Tv_le_Gv ht
  have htN : t ∈ Subgroup.normalizer (S.Uv : Set G) := hGU htG
  set ts := conjAct S.Uv ⟨t, htN⟩ with hts'
  have hts : ts ∈ autOn S.Tv S.Uv := Setup.mem_autOn_iff.2 ⟨⟨t, htN⟩, ht, rfl⟩
  have htsG : ts ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
    S.autOn_le_GvS S.Tv_le_Gv hts
  have htsJ := S.GvS_le_normalizer_JGv htsG
  set Ks := autOn K S.Uv with hKs
  set K₂s := autOn (K.map (MulAut.conj t).toMonoidHom) S.Uv with hK₂s
  have hK₂eq : K₂s = B6.conjSub ts Ks := autOn_map_conj hKU ⟨t, htN⟩
  have hq : CFSG.IsQuasisimple ↥Ks := B1Red.isQuasisimple_of_open hgood.1.2.2
  have hgood₂ : S.GoodComp K₂s := hK₂eq ▸ S.isGoodComp_conj hgood hts
  have hJG := S.JGv_le_GvS
  have hc₁ : IsComponentOf Ks S.JGv :=
    isComponentOf_of_le hgood.1 (S.goodComp_le_JGv hgood) hJG
  have hc₂ : IsComponentOf K₂s S.JGv :=
    isComponentOf_of_le hgood₂.1 (S.goodComp_le_JGv hgood₂) hJG
  have hK₂map : K₂s = Ks.map (MulAut.conj ts).toMonoidHom := hK₂eq
  have e' : ↥K₂s ≃* ↥Ks :=
    (MulEquiv.subgroupCongr hK₂map).trans
      (Ks.equivMapOfInjective (MulAut.conj ts).toMonoidHom (MulAut.conj ts).injective).symm
  obtain ⟨W₁, W₂, hWsup, hWinf, hinv₁, hinv₂, hW₁, hW₂, hN1, hCK₂⟩ :=
    swap_case3 (S.b56Cases_JGv h1222 h517 h56 hF' hH.hJ) hsup hinf hc hc₁ hc₂ hne.symm hK₁ hn hF
      e e'
  have hG₁J : G₁ ≤ S.JGv := hsup ▸ le_sup_left
  have hG₂J : G₂ ≤ S.JGv := hsup ▸ le_sup_right
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hsup' : G₂ ⊔ G₁ = S.JGv := by rw [sup_comm]; exact hsup
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hs : IsSimpleGroup ↥G₁ :=
    @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo h4) e
  obtain ⟨hKsG, hCK⟩ := centralizer_eq_bot_of_simple hs (isComponentOf_of_le hc₁ hK₁ hG₁J)
  have hJK₂ : S.JGv ⊓ Subgroup.centralizer (K₂s : Set (MulAut ↥S.Uv)) = G₁ :=
    inf_centralizer_eq hsup' hc' hK₂ hCK₂
  have hG₂G₁ : G₂.map (MulAut.conj ts).toMonoidHom ≤ G₁ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hJK₂]
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp htsJ x).mp (hG₂J hx), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [hK₂map] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    have h1 := hc k (hKsG ▸ hk) x hx
    show ts * k * ts⁻¹ * (ts * x * ts⁻¹) = ts * x * ts⁻¹ * (ts * k * ts⁻¹)
    calc ts * k * ts⁻¹ * (ts * x * ts⁻¹) = ts * (k * x) * ts⁻¹ := by group
      _ = ts * (x * k) * ts⁻¹ := by rw [h1]
      _ = ts * x * ts⁻¹ * (ts * k * ts⁻¹) := by group
  have hcardKs : Nat.card ↥K₂s = Nat.card ↥Ks := Nat.card_congr e'.toEquiv
  have hG₂eq : K₂s = G₂ := by
    refine Subgroup.eq_of_le_of_card_ge hK₂ ?_
    rw [hcardKs, hKsG]
    calc Nat.card ↥G₂ = Nat.card ↥(G₂.map (MulAut.conj ts).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj ts).injective).symm
      _ ≤ Nat.card ↥G₁ := Subgroup.card_le_of_le hG₂G₁
  have hG₁G₂ : G₁.map (MulAut.conj ts).toMonoidHom = G₂ := by
    rw [← hG₂eq, hK₂map, hKsG]
  have hsylJ : IsSylowTwoOf (autOn S.Tv S.Uv ⊓ S.JGv) S.JGv :=
    A4.isSylowTwoOf_inf_normal (S.isSylowTwoOf_TvS h1222 h517) hJG S.GvS_le_normalizer_JGv
  set Q := autOn S.Tv S.Uv ⊓ S.JGv with hQ
  set P := Q ⊓ G₁ with hP
  set P₂ := Q ⊓ G₂ with hP₂
  have hPsyl : IsSylowTwoOf P G₁ :=
    A4.isSylowTwoOf_inf_normal hsylJ hG₁J (normal_left_of_commute hsup hc)
  have hPG : P ≤ G₁ := inf_le_right
  have hP₂G : P₂ ≤ G₂ := inf_le_right
  have hcP : ∀ a ∈ P, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => hc a (hPG ha) b (hP₂G hb)
  have hQPP : P ⊔ P₂ = Q := by
    have h1 := card_sylow_eq_mul hsup hinf hc hsylJ
    have hinfP : P ⊓ P₂ = ⊥ := le_bot_iff.mp (hinf ▸ inf_le_inf hPG hP₂G)
    have h2 := card_sup_eq_mul_of_commute hinfP hcP
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
    rw [h2, h1]
  have hPtop : IsSylowTwoOf (P.subgroupOf G₁) ⊤ := by
    refine ⟨le_top, hPsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPG).symm, ?_⟩
    show ¬ 2 ∣ (P.subgroupOf G₁).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hPsyl.2.2
  obtain ⟨x₀, hx₀N, hx₀odd, hx₀1⟩ := exists_odd_normalizer_sl2 hn hF e hPtop
  set x : MulAut ↥S.Uv := (x₀ : MulAut ↥S.Uv) with hxdef
  have hxG₁ : x ∈ G₁ := x₀.2
  have hxN : x ∈ Subgroup.normalizer (P : Set (MulAut ↥S.Uv)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have := (Subgroup.mem_normalizer_iff.mp hx₀N ⟨p, hPG hp⟩).mp
        (Subgroup.mem_subgroupOf.mpr hp)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hp
      have hpG : p ∈ G₁ := by
        have h1 := G₁.mul_mem (G₁.mul_mem (G₁.inv_mem hxG₁) (hPG hp)) hxG₁
        rwa [show x⁻¹ * (x * p * x⁻¹) * x = p by group] at h1
      have := (Subgroup.mem_normalizer_iff.mp hx₀N ⟨p, hpG⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hp)
      exact Subgroup.mem_subgroupOf.mp this
  have hxodd : Odd (orderOf x) := by rw [hxdef, Subgroup.orderOf_coe]; exact hx₀odd
  have hx1 : x ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  have hxN₂ : x ∈ Subgroup.normalizer (P₂ : Set (MulAut ↥S.Uv)) :=
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (hc x hxG₁ p (hP₂G hp)).symm)
  have hxQ : x ∈ Subgroup.normalizer (Q : Set (MulAut ↥S.Uv)) := by
    rw [← hQPP, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN₂]
  have hxGv : x ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv := hJG (hG₁J hxG₁)
  obtain ⟨y, hyG, hyJ, r, hr, hyr⟩ := S.exists_normalizer_thompsonJ h1222 h517 hxGv hxQ
  obtain ⟨c, hcE, k, ⟨hkG, hkB⟩, hyck⟩ := S.exists_normalizer_baum h1222 h517 hyG hyJ
  have hr' : r ∈ P ⊔ P₂ := hQPP ▸ hr
  obtain ⟨r₁, hr₁, r₂, hr₂, hrr⟩ := S153L.comp_exists_mul hcP hr'
  subst hrr
  have hQts : ts * (r₁ * r₂) * ts⁻¹ ∈ P ⊔ P₂ := by
    rw [hQPP]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hts) _).mp hr.1
    · exact (Subgroup.mem_normalizer_iff.mp htsJ _).mp hr.2
  obtain ⟨s₁, hs₁, s₂, hs₂, hss⟩ := S153L.comp_exists_mul hcP hQts
  have htx : ts * x * ts⁻¹ ∈ G₂ := hG₁G₂ ▸ ⟨x, hxG₁, rfl⟩
  have hg₂ : s₂ * (ts * x * ts⁻¹) ∈ G₂ := G₂.mul_mem (hP₂G hs₂) htx
  have hm : ts * (r₁ * r₂ * x) * ts⁻¹ = s₁ * (s₂ * (ts * x * ts⁻¹)) := by
    calc ts * (r₁ * r₂ * x) * ts⁻¹ = (ts * (r₁ * r₂) * ts⁻¹) * (ts * x * ts⁻¹) := by group
      _ = s₁ * s₂ * (ts * x * ts⁻¹) := by rw [hss]
      _ = s₁ * (s₂ * (ts * x * ts⁻¹)) := by group
  have hTz : ∀ p ∈ autOn S.Tv S.Uv, p S.zU = S.zU := by
    intro p hp
    obtain ⟨⟨t', ht'N⟩, ht', rfl⟩ := Setup.mem_autOn_iff.1 hp
    exact Subtype.ext (by
      rw [InternalSec.coe_conjAct_apply]
      exact S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht').1)
  have htz : ts S.zU = S.zU := hTz ts hts
  have htz' : ts⁻¹ S.zU = S.zU := by
    conv_lhs => rw [← htz]
    exact MulAut.inv_apply_self _ ts S.zU
  have hPu : ∀ p ∈ P, p S.zU = S.zU := fun p hp => hTz p hp.1.1
  have hzW₂ : S.zU ∉ W₂ := by
    intro hz
    have htJ' : ∀ j ∈ S.JGv, ts⁻¹ * j * ts ∈ S.JGv := by
      intro j hj
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htsJ) j).mp hj
      simpa using this
    have htG' : ∀ g ∈ G₂, ts⁻¹ * g * ts ∈ G₁ := by
      intro g hg
      rw [← hG₁G₂] at hg
      obtain ⟨g₁, hg₁, rfl⟩ := hg
      show ts⁻¹ * (ts * g₁ * ts⁻¹) * ts ∈ G₁
      rw [show ts⁻¹ * (ts * g₁ * ts⁻¹) * ts = g₁ by group]
      exact hg₁
    have hW₁' : commV G₁ ≤ W₁ := by rw [hW₁]; exact le_sup_left
    have h1 := triv_of_mem_W2 hsup hc hW₁' hinv₂ hWinf htJ' htG' htz hz
    have h2 := S.forall_Uv_of_zU S.GvS_le_normalizer_JGv h1
    have hU2 : ∀ u : ↥S.Uv, u * u = 1 := fun u => Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two, hUe.2 _ u.2, Subgroup.coe_one])
    have h3 : ∀ j ∈ S.JGv, j * j = 1 := fun j hj => mul_self_eq_one_of_triv hU2 h2 hj
    apply not_le_centralizer_self_of_qs hq
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hab := h3 (a * b) (S.JGv.mul_mem (hc₁.1 ha) (hc₁.1 hb))
    have ha2 := h3 a (hc₁.1 ha)
    have hb2 := h3 b (hc₁.1 hb)
    calc b * a = a⁻¹ * (a * b * (a * b)) * b⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by rw [hab]; group
      _ = a * b := by rw [inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
  obtain ⟨i1, i2, i3, i4, i5⟩ := four_ne (G₁ := G₁) (G₂ := G₂) (P := P) hc hWsup hWinf
    (fun g hg => hinv₁ g (hsup ▸ hg)) (fun g hg => hinv₂ g (hsup ▸ hg))
    (fun g hg c hc' => (mem_fixV.mp hc') g (hsup ▸ hg)) hW₁ hW₂ hN1 hPsyl.2.1 hPG hxG₁ hxN
    hxodd hx1 hzW₂ hPu hr₁ (hP₂G hr₂) hs₁ hg₂
  obtain ⟨n', hn'⟩ : ∃ n' : MulAut ↥S.Uv, r₁ * r₂ * x = n' := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂'⟩ : ∃ g₂ : MulAut ↥S.Uv, s₂ * (ts * x * ts⁻¹) = g₂ := ⟨_, rfl⟩
  rw [hn'] at hyr hm i1 i2 i3 i4 i5
  rw [hg₂'] at hm i4 i5
  have hm' : s₁ * g₂ = ts * n' * ts⁻¹ := hm.symm
  have hmz : (s₁ * g₂) S.zU = ts (n' S.zU) := by
    rw [hm', MulAut.mul_apply, MulAut.mul_apply, htz']
  have i6 : S.zU ≠ (s₁ * g₂) S.zU := by
    intro h
    rw [hmz] at h
    apply i1
    have := congrArg (fun u => ts⁻¹ u) h
    simp only [MulAut.inv_apply_self] at this
    rw [htz'] at this
    exact this
  have hzE : S.z ∈ omegaOneCenterOf (thompsonJ S.Tv) := by
    rw [show S.Tv = T ⊓ Subgroup.centralizer ({S.v12} : Set G) from rfl, S.lemma_13_6_4.2]
    exact S.V2_le_omegaOneCenter_J (S.V1_le_V2 (S.mem_V1.2 (Or.inr rfl)))
  have hyE : y ∈ Subgroup.normalizer (omegaOneCenterOf (thompsonJ S.Tv) : Set G) :=
    A4.normalizer_le_normalizer_omegaOneCenterOf _ hyJ
  have hcw : ∀ w ∈ omegaOneCenterOf (thompsonJ S.Tv), c⁻¹ * w * c = w := by
    intro w hw
    have := Subgroup.mem_centralizer_iff.mp hcE w hw
    calc c⁻¹ * w * c = c⁻¹ * (w * c) := by group
      _ = c⁻¹ * (c * w) := by rw [this]
      _ = w := by group
  have hyz : y * S.z * y⁻¹ ∈ omegaOneCenterOf (thompsonJ S.Tv) :=
    (Subgroup.mem_normalizer_iff.mp hyE _).mp hzE
  have hyyz : y * (y * S.z * y⁻¹) * y⁻¹ ∈ omegaOneCenterOf (thompsonJ S.Tv) :=
    (Subgroup.mem_normalizer_iff.mp hyE _).mp hyz
  have hk : k = c⁻¹ * y := by rw [hyck, inv_mul_cancel_left]
  have hnz : ((n' S.zU : ↥S.Uv) : G) = y * S.z * y⁻¹ := by
    rw [← hyr, InternalSec.coe_conjAct_apply]
    rfl
  have hnnz : (((n' * n') S.zU : ↥S.Uv) : G) = y * (y * S.z * y⁻¹) * y⁻¹ := by
    rw [MulAut.mul_apply]
    rw [show n' (n' S.zU) = conjAct S.Uv ⟨y, hGU hyG⟩ (n' S.zU) by rw [hyr]]
    rw [InternalSec.coe_conjAct_apply, hnz]
  have hmzG : (((s₁ * g₂) S.zU : ↥S.Uv) : G) = t * (y * S.z * y⁻¹) * t⁻¹ := by
    rw [hmz, hts', InternalSec.coe_conjAct_apply, hnz]
  have e1 : k * S.z * k⁻¹ = ((n' S.zU : ↥S.Uv) : G) := by
    rw [hnz, hk]
    calc c⁻¹ * y * S.z * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * S.z * y⁻¹) * c := by group
      _ = y * S.z * y⁻¹ := hcw _ hyz
  have e2 : k * k * S.z * (k * k)⁻¹ = (((n' * n') S.zU : ↥S.Uv) : G) := by
    rw [hnnz, hk]
    calc c⁻¹ * y * (c⁻¹ * y) * S.z * (c⁻¹ * y * (c⁻¹ * y))⁻¹ =
        c⁻¹ * (y * (c⁻¹ * (y * S.z * y⁻¹) * c) * y⁻¹) * c := by group
      _ = c⁻¹ * (y * (y * S.z * y⁻¹) * y⁻¹) * c := by rw [hcw _ hyz]
      _ = y * (y * S.z * y⁻¹) * y⁻¹ := hcw _ hyyz
  have htzG : t⁻¹ * S.z * t = S.z := by
    have := S.conj_z_of_mem_T (T.inv_mem (Subgroup.mem_inf.mp ht).1)
    rwa [inv_inv] at this
  have e3 : t * k * t⁻¹ * S.z * (t * k * t⁻¹)⁻¹ = (((s₁ * g₂) S.zU : ↥S.Uv) : G) := by
    rw [hmzG, ← (show k * S.z * k⁻¹ = y * S.z * y⁻¹ by rw [e1, hnz])]
    calc t * k * t⁻¹ * S.z * (t * k * t⁻¹)⁻¹ = t * k * (t⁻¹ * S.z * t) * k⁻¹ * t⁻¹ := by group
      _ = t * (k * S.z * k⁻¹) * t⁻¹ := by rw [htzG]; group
  have hB : baum S.Tv = baum T := S.lemma_13_6_4.1
  have hMV : ∀ a ∈ Subgroup.centralizer ({S.v12} : Set G),
      a ∈ Subgroup.normalizer (baum S.Tv : Set G) →
        a ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer ({S.v12} : Set G) :=
    fun a ha hb => S.lemma_13_6_5 h1222 h517 ⟨ha, hB ▸ hb⟩
  have htB : t ∈ Subgroup.normalizer (baum S.Tv : Set G) :=
    normalizer_le_normalizer_baum S.Tv (Subgroup.le_normalizer ht)
  have h0 := hMV 1 (Subgroup.one_mem _) (Subgroup.one_mem _)
  have h1' := hMV k hkG hkB
  have h2' := hMV (k * k) (Subgroup.mul_mem _ hkG hkG) (Subgroup.mul_mem _ hkB hkB)
  have h3' := hMV (t * k * t⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ htG hkG)
    (Subgroup.inv_mem _ htG)) (Subgroup.mul_mem _ (Subgroup.mul_mem _ htB hkB)
    (Subgroup.inv_mem _ htB))
  refine S.false_of_four_conj (a := ![1, k, k * k, t * k * t⁻¹]) (fun i => ?_) (fun i => ?_) ?_
  · fin_cases i
    exacts [h0.1, h1'.1, h2'.1, h3'.1]
  · fin_cases i
    exacts [h0.2, h1'.2, h2'.2, h3'.2]
  · have e0 : 1 * S.z * 1⁻¹ = ((S.zU : ↥S.Uv) : G) := by simp [Setting.zU]
    have hval : ∀ l : Fin 4, (![1, k, k * k, t * k * t⁻¹] l) * S.z *
        (![1, k, k * k, t * k * t⁻¹] l)⁻¹ =
          ((![S.zU, n' S.zU, (n' * n') S.zU, (s₁ * g₂) S.zU] l : ↥S.Uv) : G) := by
      intro l
      fin_cases l
      exacts [e0, e1, e2, e3]
    intro i j hij hcontra
    rw [hval i, hval j] at hcontra
    have hb := Subtype.ext hcontra
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact i1 hb | exact i1 hb.symm | exact i2 hb | exact i2 hb.symm
      | exact i3 hb | exact i3 hb.symm | exact i4 hb | exact i4 hb.symm
      | exact i5 hb | exact i5 hb.symm | exact i6 hb | exact i6 hb.symm

end CFSG.Quasithin.H13.A5
