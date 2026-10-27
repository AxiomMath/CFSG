module

public import CFSG.Quasithin.Vol2.KGFactJ4M4Card
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Fac
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Hj
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4GD

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L52

theorem card_of_lieModel_l52 {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X CFSG.Assembly.LowTwoRank.StatedLieTag.PSL 5 2 1) :
    Nat.card X = 9999360 := by
  rcases h with ⟨-, ⟨-, K, _, _, hK, ⟨e⟩⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 5), hK]
    decide
  all_goals exact absurd h0 (by norm_num)

theorem card_eq_card_pCore_mul {X : Type*} [Group X] (Y : Subgroup X) :
    Nat.card Y = Nat.card (CFSG.pCore 2 ↥Y) * Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y), mul_comm]

theorem card_map_conj {X : Type*} [Group X] (H : Subgroup X) (g : X) :
    Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isHat_map_conj {X : Type} [Group X] {B : Subgroup X} (g : X) {T : Type} [Group T]
    (h : IsHat (↥B ⧸ CFSG.pCore 2 ↥B) T) :
    IsHat (↥(B.map (MulAut.conj g).toMonoidHom) ⧸
      CFSG.pCore 2 ↥(B.map (MulAut.conj g).toMonoidHom)) T :=
  IsHat.of_mulEquiv (J4.pCoreQuotEquiv (B.equivMapOfInjective _ (MulAut.conj g).injective)) h

theorem comap_le_of_le_map_conj {X : Type} [Group X] {B Y : Subgroup X} {g : X}
    (hg : Y ≤ B.map (MulAut.conj g).toMonoidHom) :
    Y.comap ((⊤ : Subgroup X).subtype.comp
      (Subgroup.topEquiv.trans (MulAut.conj g⁻¹)).symm.toMonoidHom) ≤ B := by
  intro x hx
  rw [Subgroup.mem_comap] at hx
  have hx' : g * x * g⁻¹ ∈ Y := by
    have e : ((⊤ : Subgroup X).subtype.comp
        (Subgroup.topEquiv.trans (MulAut.conj g⁻¹)).symm.toMonoidHom) x = g * x * g⁻¹ := by
      simp
    rwa [e] at hx
  obtain ⟨m, hm, hmx⟩ := hg hx'
  have : m = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmx
    calc m = g⁻¹ * (g * m * g⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hmx]
      _ = x := by group
  rw [← this]
  exact hm

end L52

@[expose] def ModelL52 (X : Type) [Group X] (P : Subgroup X → Prop) : Prop :=
  ∀ (Y V S : Subgroup X) (z : X), P Y → Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 9999360 →
    V ≤ centerOf (pCoreOf 2 Y) → V ≠ ⊥ → IsSylowTwoOf S Y → z ∈ V → z ≠ 1 →
    z ∈ Subgroup.centralizer (S : Set X) →
    IsHat (↥(perfectCore (Subgroup.centralizer ({z} : Set X))) ⧸
        CFSG.pCore 2 ↥(perfectCore (Subgroup.centralizer ({z} : Set X))))
      (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
    (⊤ : Subgroup X) = Y ⊔ perfectCore (Subgroup.centralizer ({z} : Set X))

theorem genL52_of_mulEquiv {X : Type} [Group X] [Finite X] {P : Subgroup X → Prop}
    (hX : ModelL52 X P) {G : Type} [Group G] [Finite G] {K Y V S : Subgroup G} {z : G}
    (ψ : ↥K ≃* X) (hYK : Y ≤ K) (hP : P (Y.comap (K.subtype.comp ψ.symm.toMonoidHom)))
    (hYq : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 9999360)
    (hV : V ≤ centerOf (pCoreOf 2 Y)) (hV1 : V ≠ ⊥) (hS : IsSylowTwoOf S Y)
    (hzV : z ∈ V) (hz1 : z ≠ 1) (hzS : z ∈ Subgroup.centralizer (S : Set G)) :
    IsHat (↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))) ⧸
        CFSG.pCore 2 ↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))))
      (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
    K = Y ⊔ perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
  set ι : X →* G := K.subtype.comp ψ.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := K.subtype_injective.comp ψ.symm.injective
  have hιr : ι.range = K := by
    rw [hιdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap : ∀ {A : Subgroup G}, A ≤ K → (A.comap ι).map ι = A := fun hA => by
    rw [Subgroup.map_comap_eq, hιr, inf_of_le_right hA]
  have hVO : V ≤ pCoreOf 2 Y := fun v hv => (hV hv).1
  have hVK : V ≤ K := hVO.trans ((pCoreOf_le 2 Y).trans hYK)
  have hYm : (Y.comap ι).map ι = Y := hmap hYK
  have hVm : (V.comap ι).map ι = V := hmap hVK
  have hSm : (S.comap ι).map ι = S := hmap (hS.1.trans hYK)
  have hzK : z ∈ K := hVK hzV
  have hιz : ι (ψ ⟨z, hzK⟩) = z := by simp [hιdef]
  have hYq' : Nat.card (↥(Y.comap ι) ⧸ CFSG.pCore 2 ↥(Y.comap ι)) = 9999360 := by
    rw [← hYq]
    exact Nat.card_congr (J4.pCoreQuotEquiv (((Y.comap ι).equivMapOfInjective ι hι).trans
      (MulEquiv.subgroupCongr hYm))).toEquiv
  have hV' : V.comap ι ≤ centerOf (pCoreOf 2 (Y.comap ι)) := by
    rw [← Subgroup.map_le_map_iff_of_injective hι, map_centerOf_of_injective ι hι,
      map_pCoreOf_of_injective ι hι, hYm, hVm]
    exact hV
  have hV1' : V.comap ι ≠ ⊥ := fun h => hV1 (by rw [← hVm, h, Subgroup.map_bot])
  have hS' : IsSylowTwoOf (S.comap ι) (Y.comap ι) :=
    (isSylowTwoOf_map_iff ι hι).mp (by rw [hSm, hYm]; exact hS)
  have hzV' : ψ ⟨z, hzK⟩ ∈ V.comap ι := by
    rw [Subgroup.mem_comap, hιz]
    exact hzV
  have hz1' : ψ ⟨z, hzK⟩ ≠ 1 := fun h => hz1 (by rw [← hιz, h, map_one])
  have hzS' : ψ ⟨z, hzK⟩ ∈ Subgroup.centralizer ((S.comap ι : Subgroup X) : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => hι ?_
    rw [map_mul, map_mul, hιz]
    exact Subgroup.mem_centralizer_iff.mp hzS (ι s) hs
  obtain ⟨hhat, htop⟩ := hX _ _ _ _ hP hYq' hV' hV1' hS' hzV' hz1' hzS'
  have hKZ : (perfectCore (Subgroup.centralizer ({ψ ⟨z, hzK⟩} : Set X))).map ι =
      perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [map_perfectCore, map_centralizer_of_injective ι hι, hιr, Set.image_singleton, hιz]
  refine ⟨?_, ?_⟩
  · have e : ↥(perfectCore (Subgroup.centralizer ({ψ ⟨z, hzK⟩} : Set X))) ≃*
        ↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))) :=
      ((perfectCore (Subgroup.centralizer ({ψ ⟨z, hzK⟩} : Set X))).equivMapOfInjective ι
        hι).trans (MulEquiv.subgroupCongr hKZ)
    exact IsHat.of_mulEquiv (J4.pCoreQuotEquiv e) hhat
  · have h1 := congrArg (Subgroup.map ι) htop
    rwa [Subgroup.map_sup, hYm, hKZ, ← MonoidHom.range_eq_map, hιr] at h1

namespace L52

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin.B5.Ln (mat)
open scoped Matrix

theorem eq_M4_of_le
    {Y V : Subgroup J}
    (hYM : Y ≤ CFSG.Quasithin.KGJ4.M4) (hYq : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 9999360)
    (hV : V ≤ centerOf (pCoreOf 2 Y)) (hV1 : V ≠ ⊥) :
    Y = CFSG.Quasithin.KGJ4.M4 ∧ pCoreOf 2 Y = F4 j4Facts.mat chkF_true := by
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  set M := CFSG.Quasithin.KGJ4.M4 with hMdef
  set F := F4 j4Facts.mat chkF_true with hFdef
  set π := piM4 j4Facts.mat chkF_true with hπdef
  have hcard : Nat.card ↥M = 10239344640 := J4M4Card.card_M4
  have hFn := normal_F4 j4Facts.mat chkF_true
  have hker := ker_piM4 j4Facts.mat chkF_true hcard
  have hYFn : ((Y ⊓ F).subgroupOf Y).Normal := ⟨fun x hx y => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ y.2 hx.1) (Subgroup.inv_mem _ y.2), ?_⟩
    have h := hFn.conj_mem ⟨x, hYM hx.1⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx.2)
      ⟨y, hYM y.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h⟩
  have hYFO : Y ⊓ F ≤ pCoreOf 2 Y :=
    le_pCoreOf 2 inf_le_left hYFn ((isPGroup_F4 j4Facts.mat chkF_true).to_le inf_le_right)
  have hcO : Nat.card ↥(pCoreOf 2 Y) = Nat.card ↥(CFSG.pCore 2 ↥Y) := by
    rw [pCoreOf]
    exact Subgroup.card_map_of_injective Y.subtype_injective
  have hcY : Nat.card ↥Y = Nat.card ↥(pCoreOf 2 Y) * 9999360 := by
    rw [card_eq_card_pCore_mul, hYq, hcO]
  let f : ↥Y →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) :=
    π.comp (Subgroup.inclusion hYM)
  have hfker : ∀ y : ↥Y, y ∈ f.ker ↔ (y : J) ∈ F := fun y => by
    rw [MonoidHom.mem_ker]
    show π (Subgroup.inclusion hYM y) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rfl
  have hck : Nat.card ↥f.ker = Nat.card ↥(Y ⊓ F) := by
    have e : f.ker = (Y ⊓ F).subgroupOf Y := by
      ext y
      rw [hfker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
    rw [e, ← Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_left]
  have h1 := f.ker.card_mul_index
  rw [Subgroup.index_ker, hck] at h1
  have hk : Nat.card ↥(Y ⊓ F) ≤ Nat.card ↥(pCoreOf 2 Y) := Subgroup.card_le_of_le hYFO
  have hr : Nat.card ↥f.range ≤ 9999360 := by
    rw [← card_statedSL5']
    exact Subgroup.card_le_card_group _
  have hpos : 0 < Nat.card ↥(Y ⊓ F) := Nat.card_pos
  have hpos' : 0 < Nat.card ↥f.range := Nat.card_pos
  have hr' : Nat.card ↥f.range = 9999360 := by
    by_contra hne
    have hlt : Nat.card ↥f.range < 9999360 := lt_of_le_of_ne hr hne
    have : Nat.card ↥(Y ⊓ F) * Nat.card ↥f.range < Nat.card ↥(pCoreOf 2 Y) * 9999360 :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hlt hpos) (Nat.mul_le_mul_right _ hk)
    omega
  have hk' : Nat.card ↥(Y ⊓ F) = Nat.card ↥(pCoreOf 2 Y) := by
    rw [hr', hcY] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hYFO' : Y ⊓ F = pCoreOf 2 Y := Subgroup.eq_of_le_of_card_ge hYFO hk'.ge
  have hrange : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hr', card_statedSL5'])
  have hMYF : M ≤ Y ⊔ F := by
    intro m hm
    obtain ⟨y, hy⟩ : π ⟨m, hm⟩ ∈ f.range := hrange ▸ Subgroup.mem_top _
    have hyk : (Subgroup.inclusion hYM y)⁻¹ * ⟨m, hm⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hy]
      exact inv_mul_cancel _
    rw [hker, Subgroup.mem_subgroupOf] at hyk
    have e : m = (y : J) * ((y : J)⁻¹ * m) := by group
    rw [e]
    exact Subgroup.mul_mem_sup y.2 (by simpa using hyk)
  have hnorm : M ≤ Subgroup.normalizer ((Y ⊓ F : Subgroup J) : Set J) := by
    refine hMYF.trans (sup_le ?_ ?_)
    · intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have key : ∀ u ∈ Y, ∀ w ∈ Y ⊓ F, u * w * u⁻¹ ∈ Y ⊓ F := fun u hu w hw => by
        have := hYFn.conj_mem ⟨w, hw.1⟩ (by rw [Subgroup.mem_subgroupOf]; exact hw) ⟨u, hu⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      refine ⟨fun hx => key y hy x hx, fun hx => ?_⟩
      have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hx
      simpa [mul_assoc] using this
    · intro f' hf'
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hcomm : ∀ w ∈ F, f' * w * f'⁻¹ = w := fun w hw => by
        rw [eSub_comm (fJ_basis j4Facts.mat chkF_true) f' w hf' hw, mul_inv_cancel_right]
      constructor
      · intro hx
        rw [hcomm x hx.2]
        exact hx
      · intro hx
        have hxF : x ∈ F := by
          have h2 := hx.2
          rwa [hcomm x (by
            have e : x = f'⁻¹ * (f' * x * f'⁻¹) * f' := by group
            rw [e]
            exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hf') h2) hf')] at h2
        rwa [hcomm x hxF] at hx
  rcases m4_min j4Facts.mat chkF_true (Y ⊓ F) inf_le_right hnorm with hb | htop
  · exfalso
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    have := (hV hv).1
    rw [← hYFO', hb] at this
    exact this
  · have hFY : F ≤ Y := by
      intro x hx
      have hx' : x ∈ Y ⊓ F := by rw [htop]; exact hx
      exact hx'.1
    have hYeq : Y = M := le_antisymm hYM (hMYF.trans (sup_le le_rfl hFY))
    exact ⟨hYeq, by rw [← hYFO', htop]⟩

theorem fix_F_of_sylow
    {S : Subgroup J}
    (hS : IsSylowTwoOf S CFSG.Quasithin.KGJ4.M4) :
    ∃ w : J, ∀ x ∈ F4 j4Facts.mat chkF_true, x ∈ Subgroup.centralizer (S : Set J) →
      x = 1 ∨ x = w := by
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := CFSG.Quasithin.KGJ4.M4 with hMdef
  set π := piM4 j4Facts.mat chkF_true with hπdef
  have hb := fJ_basis j4Facts.mat chkF_true
  have hFn := normal_F4 j4Facts.mat chkF_true
  have hker := ker_piM4 j4Facts.mat chkF_true J4M4Card.card_M4
  let T : Subgroup ↥M := unitri5.comap π
  have hU : IsPGroup 2 ↥unitri5 := IsPGroup.of_card card_unitri5
  have hT : IsPGroup 2 ↥T := by
    intro t
    obtain ⟨k, hk⟩ := hU ⟨π t, t.2⟩
    have hk' : π ((t : ↥M) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hkF : (t : ↥M) ^ 2 ^ k ∈ (F4 j4Facts.mat chkF_true).subgroupOf M := by
      rw [← hker]
      exact hk'
    rw [Subgroup.mem_subgroupOf] at hkF
    obtain ⟨k', hk''⟩ := isPGroup_F4 j4Facts.mat chkF_true ⟨_, hkF⟩
    refine ⟨k + k', Subtype.ext (Subtype.ext ?_)⟩
    have e := congrArg Subtype.val hk''
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at e
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
    simpa using e
  have hS0 : IsPGroup 2 ↥(S.subgroupOf M) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let PS : Sylow 2 ↥M := hS0.toSylow hS.2.2
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥M PS Q
  have hTy : ∀ t ∈ T, ∃ s ∈ S, ((t : ↥M) : J) = (y : J) * s * (y : J)⁻¹ := by
    intro t ht
    have h1 : t ∈ (Q : Subgroup ↥M) := hTQ ht
    rw [← hy, Sylow.coe_subgroup_smul] at h1
    obtain ⟨s, hs, hst⟩ := (Subgroup.mem_smul_pointwise_iff_exists t (MulAut.conj y) _).1 h1
    have hs' : s ∈ S.subgroupOf M := hs
    rw [Subgroup.mem_subgroupOf] at hs'
    refine ⟨(s : J), hs', ?_⟩
    rw [← hst]
    simp [MulAut.conj_apply]
  refine ⟨(y : J)⁻¹ * eElt fJ (codeVec 512) * (y : J), fun x hxF hxS => ?_⟩
  have hx' : (y : J) * x * (y : J)⁻¹ ∈ F4 j4Facts.mat chkF_true := by
    have := hFn.conj_mem ⟨x, F4_le_M4 _ _ hxF⟩ (by rw [Subgroup.mem_subgroupOf]; exact hxF) y
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  obtain ⟨v, hv⟩ := (mem_eSub_iff hb _).1 hx'
  obtain ⟨c, hc, rfl⟩ := exists_codeVec v
  have hfix : ∀ p : Fin 10, psiMat (tvEl p) *ᵥ codeVec c = codeVec c := by
    intro p
    obtain ⟨t, ht⟩ := piM4_surjective j4Facts.mat chkF_true (tvEl p)
    have htT : t ∈ T := by
      show π t ∈ unitri5
      rw [ht]
      exact tvEl_mem p
    obtain ⟨s, hs, hts⟩ := hTy t htT
    have hsx : s * x = x * s := Subgroup.mem_centralizer_iff.mp hxS s hs
    have hcomm : (t : J) * ((y : J) * x * (y : J)⁻¹) * (t : J)⁻¹ =
        (y : J) * x * (y : J)⁻¹ := by
      have hts' : (t : J) = (y : J) * s * (y : J)⁻¹ := hts
      rw [hts']
      calc (y : J) * s * (y : J)⁻¹ * ((y : J) * x * (y : J)⁻¹) * ((y : J) * s * (y : J)⁻¹)⁻¹
          = (y : J) * (s * x) * s⁻¹ * (y : J)⁻¹ := by group
        _ = (y : J) * x * (y : J)⁻¹ := by rw [hsx]; group
    have h2 := piM4_conj j4Facts.mat chkF_true t (codeVec c)
    rw [hv, hcomm, ← hv, ht] at h2
    exact (eElt_injective hb h2).symm
  have hc' : c = 0 ∨ c = 512 := by
    refine fixU_chk c hc fun p => ?_
    have e2 := congrArg altV (hfix p)
    rw [altV_psiMat_codeVec (rfl : mat (tvEl p)⁻¹ = D35Chk.bm (tvU p)), altV_codeVec] at e2
    exact D35Chk.bm_inj (D35Chk.bmul_lt _ _) (D35Chk.colSum_lt D35Chk.altE_lt c) e2
  have hxe : x = (y : J)⁻¹ * ((y : J) * x * (y : J)⁻¹) * (y : J) := by group
  rcases hc' with rfl | rfl
  · left
    have h0 : codeVec 0 = 0 := by
      funext i
      simp [codeVec]
    rw [h0, eElt_zero] at hv
    rw [hxe, ← hv]
    group
  · right
    rw [hxe, ← hv]

theorem exists_conj_z0
    {S : Subgroup J} (hS : IsSylowTwoOf S CFSG.Quasithin.KGJ4.M4)
    {z : J} (hzF : z ∈ F4 j4Facts.mat chkF_true) (hz1 : z ≠ 1)
    (hzS : z ∈ Subgroup.centralizer (S : Set J)) :
    ∃ g : J, z = g * CFSG.Quasithin.J4Loc.z0 * g⁻¹ := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := J4M4Card.card_M4
  obtain ⟨w, hw⟩ := fix_F_of_sylow hS
  have hFS : F4 j4Facts.mat chkF_true ≤ S := by
    have := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
    rwa [pCoreOf_M4 _ _ hcard] at this
  have hZF : ∀ x ∈ S, x ∈ Subgroup.centralizer (S : Set J) → x ∈ F4 j4Facts.mat chkF_true :=
    fun x hxS hxC => m4_CE _ _ hcard ⟨hS.1 hxS, Subgroup.centralizer_le hFS hxC⟩
  have hzw : z = w := (hw z hzF hzS).resolve_left hz1
  have hcS : Nat.card ↥S = 2 ^ 20 := by
    have h1 := (S.subgroupOf CFSG.Quasithin.KGJ4.M4).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hcard] at h1
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS.2.1
    rw [hk] at h1 ⊢
    have hodd := hS.2.2
    have h2 := congrArg (fun n => n.factorization 2) h1
    rw [factorization_two_pow_mul hodd (fun h0 => by rw [h0] at h1; norm_num at h1),
      show (10239344640 : ℕ) = 2 ^ 20 * 9765 by norm_num,
      factorization_two_pow_mul (by norm_num) (by norm_num)] at h2
    rw [h2]
  obtain ⟨P, hSP⟩ := hS.2.1.exists_le_sylow
  have hcP : Nat.card ↥(P : Subgroup J) = 2 ^ 21 := by
    rw [Sylow.card_eq_multiplicity, card_J_factorization hF]
  have hidx : (S.subgroupOf (P : Subgroup J)).index = 2 := by
    have h1 := (S.subgroupOf (P : Subgroup J)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv, hcS, hcP] at h1
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h1.trans (by norm_num))
  have hSn : (S.subgroupOf (P : Subgroup J)).Normal := Subgroup.normal_of_index_eq_two hidx
  have hconjS : ∀ q ∈ (P : Subgroup J), ∀ s ∈ S, q * s * q⁻¹ ∈ S := fun q hq s hs => by
    have := hSn.conj_mem ⟨s, hSP hs⟩ (by rw [Subgroup.mem_subgroupOf]; exact hs) ⟨q, hq⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hzS' : z ∈ S := hFS hzF
  have hzP : ∀ q ∈ (P : Subgroup J), q * z * q⁻¹ = z := by
    intro q hq
    have h1 : q * z * q⁻¹ ∈ S := hconjS q hq z hzS'
    have h2 : q * z * q⁻¹ ∈ Subgroup.centralizer (S : Set J) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' : q⁻¹ * s * q⁻¹⁻¹ ∈ S := hconjS q⁻¹ (Subgroup.inv_mem _ hq) s hs
      rw [inv_inv] at hs'
      have h3 := Subgroup.mem_centralizer_iff.mp hzS (q⁻¹ * s * q) hs'
      calc s * (q * z * q⁻¹) = q * ((q⁻¹ * s * q) * z) * q⁻¹ := by group
        _ = q * (z * (q⁻¹ * s * q)) * q⁻¹ := by rw [h3]
        _ = q * z * q⁻¹ * s := by group
    rcases hw _ (hZF _ h1 h2) h2 with h4 | h4
    · exfalso
      apply hz1
      have e : z = q⁻¹ * (q * z * q⁻¹) * q := by group
      rw [e, h4]
      group
    · rw [h4, ← hzw]
  obtain ⟨g, hg⟩ := exists_conj_le_P0 hM hF (P : Subgroup J) P.isPGroup'
  have hPeq : (P : Subgroup J).map (MulAut.conj g⁻¹).toMonoidHom = P0 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨q, hq, rfl⟩
      simpa [MulAut.conj_apply] using hg q hq
    · rw [card_map_conj, hcP, card_P0 hM hF]
  have hz0 : g⁻¹ * z * g ∈ centerOf P0 := by
    refine ⟨hg z (hSP hzS'), Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
    rw [← hPeq] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := hzP q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * q * g * (g⁻¹ * z * g) = g⁻¹ * (q * z * q⁻¹) * q * g := by group
      _ = g⁻¹ * z * q * g := by rw [this]
      _ = g⁻¹ * z * g * (g⁻¹ * q * g) := by group
  have e : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
  rcases CFSG.Quasithin.J4Local.eq_one_or_eq_zJ_of_mem_centerOf hz0 with h | h
  · exfalso
    apply hz1
    rw [e, h]
    group
  · exact ⟨g, by rw [e, h]; rfl⟩

end L52

end CFSG.Quasithin.H13.Ch4.G443J4
