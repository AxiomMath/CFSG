module

public import CFSG.Quasithin.Vol2.Ch7Sec77Conf
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.Quasithin.Vol2.Ch7Sec77Comp

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem map_conj_eq_of_commute {A : Subgroup G} {y : G} (h : ∀ a ∈ A, y * a = a * y) :
    A.map (MulAut.conj y).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change y * a * y⁻¹ ∈ A
    rw [h a ha, mul_inv_cancel_right]
    exact ha
  · intro hx
    refine ⟨x, hx, ?_⟩
    change y * x * y⁻¹ = x
    rw [h x hx, mul_inv_cancel_right]

namespace Setup

variable (S : Setup T L I)
include S

variable {S}

namespace Conf

variable {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G} {Vp H : Subgroup G}
  (C : S.Conf θ e Vp H)
include C

theorem a23List_KBar (h23 : A23SQTKListFact) {K : Subgroup G} (hK : IsComponentIn K H)
    (hqQ : CFSG.IsQuasisimple (KQ K)) : A23List (KBar K) := by
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian C.pCoreOf_ne_bot
  set ψ : ↥(K.subgroupOf H) →* KBar K :=
    (piK K).comp (Subgroup.subgroupOfEquivOfLe hK.1).toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    (piK_surjective K).comp (Subgroup.subgroupOfEquivOfLe hK.1).surjective
  set e' : ↥(K.subgroupOf H) ⧸ ψ.ker ≃* KBar K :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψs with he'
  obtain ⟨hs, a, b, hab⟩ := isSimpleGroup_KBar hqQ
  have hs' : IsSimpleGroup (↥(K.subgroupOf H) ⧸ ψ.ker) := by
    have := hs
    exact e'.isSimpleGroup
  have hab' : ∃ a b : ↥(K.subgroupOf H) ⧸ ψ.ker, a * b ≠ b * a :=
    ⟨e'.symm a, e'.symm b, fun h0 => hab (by simpa using congrArg e' h0)⟩
  exact A36A.a23List_of_mulEquiv e'.symm (h23 ↥H hSQ (K.subgroupOf H) ψ.ker hs' hab')

theorem exists_E (h3108 : Stmt3_2_10_eight) (h755 : Input7_5_5) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact)
    {K : Subgroup G} (hK : IsComponentIn K H) :
    ∃ E : Subgroup (KBar K),
      E ≤ ((T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K).subgroupOf K).map (piK K) ∧
      IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
      ((T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K).subgroupOf K).map (piK K) ≤
        Subgroup.normalizer (E : Set (KBar K)) ∧
      (((T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K).subgroupOf K).map (piK K) ⊓
        Subgroup.centralizer (E : Set (KBar K))).relIndex
          (((T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K).subgroupOf K).map (piK K)) ≤ 2 ∧
      (∀ v (hv : v ∈ S.vm e), ∃ s ∈ E, phiK K ⟨v, C.vm_le_normalizer h37c h38c hK hv⟩ =
        MulAut.conj s) ∧
      ∀ s ∈ E, ∃ v ∈ S.vm e, ∃ hv : v ∈ Subgroup.normalizer (K : Set G),
        phiK K ⟨v, hv⟩ = MulAut.conj s := by
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hqQ : CFSG.IsQuasisimple (KQ K) := isQuasisimple_KQ hq
  have hvmN := C.vm_le_normalizer h37c h38c hK
  have hθN := C.th_mem_normalizer h37c h38c hK
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTp
  set TK := Tp ⊓ K with hTK
  have hTKs : IsSylowTwoOf TK K :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal C.sylH hK.1 hK.2.2
  set Pb : Subgroup (KBar K) := (TK.subgroupOf K).map (piK K) with hPb
  have hPbs : IsSylowTwoOf Pb ⊤ :=
    isSylowTwoOf_map_top (piK K) (piK_surjective K) (isSylowTwoOf_subgroupOf_top hTKs)
  have hlist := C.a23List_KBar h23 hK hqQ
  obtain ⟨hs, hnab⟩ := isSimpleGroup_KBar hqQ
  have hcenter : Subgroup.center (KBar K) = ⊥ := center_eq_bot_of_simple_ch625 hs hnab
  have hconj : Function.Injective (MulAut.conj : KBar K →* MulAut (KBar K)) := by
    intro a b hab
    have h1 : MulAut.conj (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 := mem_center_of_conj_eq_one h1
    rw [hcenter, Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp h2
  have hVTK : ∀ v ∈ S.vm e, v ∈ Subgroup.normalizer (TK : Set G) := fun v hv =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (C.V_le_tp (vm_le (S := S) hv)), hvmN hv⟩
  have hVP : ∀ v (hv : v ∈ S.vm e), Pb.map (phiK K ⟨v, hvmN hv⟩).toMonoidHom = Pb :=
    fun v hv => phiK_map_eq (hvmN hv) (hVTK v hv)
  have hinner := exists_phiK_eq_conj kf1 hqQ hlist hvmN hθN C.hc.odd
    (fun v hv => S.hV.2 v (vm_le hv)) (commutator_vm C.hc) hPbs hVP
  set V' := (S.vm e).subgroupOf (Subgroup.normalizer (K : Set G)) with hV'
  set E : Subgroup (KBar K) := (V'.map (phiK K)).comap MulAut.conj with hE
  have hmemE : ∀ s, s ∈ E ↔ ∃ v ∈ S.vm e, ∃ hv : v ∈ Subgroup.normalizer (K : Set G),
      phiK K ⟨v, hv⟩ = MulAut.conj s := by
    intro s
    constructor
    · rintro ⟨⟨v, hvN⟩, hv, h⟩
      exact ⟨v, hv, hvN, h⟩
    · rintro ⟨v, hv, hvN, h⟩
      exact ⟨⟨v, hvN⟩, hv, h⟩
  have hsv : ∀ v (hv : v ∈ S.vm e), ∃ s ∈ E, phiK K ⟨v, hvmN hv⟩ = MulAut.conj s := by
    intro v hv
    obtain ⟨s, -, hs⟩ := hinner v hv
    exact ⟨s, (hmemE s).mpr ⟨v, hv, hvmN hv, hs⟩, hs⟩
  have hφinj : ∀ v ∈ S.vm e, ∀ w ∈ S.vm e, ∀ (hv : v ∈ Subgroup.normalizer (K : Set G))
      (hw : w ∈ Subgroup.normalizer (K : Set G)), phiK K ⟨v, hv⟩ = phiK K ⟨w, hw⟩ → v = w := by
    intro v hv w hw hvN hwN h
    have hc : phiK K ⟨v * w⁻¹, Subgroup.mul_mem _ hvN (Subgroup.inv_mem _ hwN)⟩ = 1 := by
      have e1 : (⟨v * w⁻¹, Subgroup.mul_mem _ hvN (Subgroup.inv_mem _ hwN)⟩ :
          ↥(Subgroup.normalizer (K : Set G))) = ⟨v, hvN⟩ * ⟨w, hwN⟩⁻¹ := rfl
      rw [e1, map_mul, map_inv, h, mul_inv_cancel]
    have h1 := mem_centralizer_of_phiK_eq_one hq _ hc
    have h2 := C.eq_one_of_mem_centralizer h37c h38c h3108 h755 hK
      ((S.vm e).mul_mem hv ((S.vm e).inv_mem hw)) h1
    exact mul_inv_eq_one.mp h2
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, hsv, fun s hs => (hmemE s).mp hs⟩
  ·
    intro s hs
    obtain ⟨v, hv, hvN, h⟩ := (hmemE s).mp hs
    obtain ⟨s', hs'P, hs'⟩ := hinner v hv
    rw [hconj (h.symm.trans hs')]
    exact hs'P
  ·
    refine ⟨⟨⟨fun x y => Subtype.ext (hconj ?_)⟩⟩, fun x hx => hconj ?_⟩
    · obtain ⟨v, hv, hvN, hxv⟩ := (hmemE x).mp x.2
      obtain ⟨w, hw, hwN, hyw⟩ := (hmemE y).mp y.2
      have hc : (⟨v, hvN⟩ * ⟨w, hwN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨w, hwN⟩ * ⟨v, hvN⟩ := Subtype.ext (by
        change v * w = w * v
        exact congrArg Subtype.val (S.hV.1.is_comm.comm ⟨v, vm_le hv⟩ ⟨w, vm_le hw⟩))
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← hxv, ← hyw, ← map_mul,
        ← map_mul, hc]
    · obtain ⟨v, hv, hvN, hxv⟩ := (hmemE x).mp hx
      rw [map_pow, ← hxv, ← map_pow, map_one]
      have e2 : (⟨v, hvN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 = 1 :=
        Subtype.ext (by simp [S.hV.2 v (vm_le hv)])
      rw [e2, map_one]
  ·
    have hrange : V'.map (phiK K) ≤ (MulAut.conj : KBar K →* MulAut (KBar K)).range := by
      rintro _ ⟨⟨v, hvN⟩, hv, rfl⟩
      obtain ⟨s, -, hs⟩ := hinner v hv
      exact ⟨s, hs.symm⟩
    have h1 : Nat.card E = Nat.card (V'.map (phiK K)) := by
      rw [← Subgroup.card_map_of_injective hconj, hE, Subgroup.map_comap_eq_self hrange]
    have h2 : Nat.card (V'.map (phiK K)) = Nat.card V' := by
      have hinj : Set.InjOn (phiK K) (V' : Set ↥(Subgroup.normalizer (K : Set G))) := by
        rintro ⟨v, hvN⟩ hv ⟨w, hwN⟩ hw h
        exact Subtype.ext (hφinj v hv w hw hvN hwN h)
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, Subgroup.coe_map, hinj.ncard_image,
        ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    have h3 : Nat.card V' = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hvmN).toEquiv, card_vm]
    rw [h1, h2, h3]
  ·
    have key : ∀ x ∈ Pb, ∀ s ∈ E, x * s * x⁻¹ ∈ E := by
      rintro _ ⟨⟨t, htK⟩, ht, rfl⟩ s hs
      replace ht : t ∈ TK := ht
      obtain ⟨v, hv, hvN, hsv'⟩ := (hmemE s).mp hs
      obtain ⟨a, ha, b, hb, hab⟩ := C.exists_conj_eq ht.1 hv
      have haK : a ∈ Subgroup.centralizer (K : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun k hk =>
          (Subgroup.mem_centralizer_iff.mp (C.hHG (hK.1 hk)) a ha).symm
      have haN : a ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.centralizer_le_normalizer _ haK
      refine (hmemE _).mpr ⟨b, hb, hvmN hb, ?_⟩
      have htN : t ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer htK
      have e1 : (⟨t * v * t⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hvN)
          (Subgroup.inv_mem _ htN)⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨a, haN⟩ * ⟨b, hvmN hb⟩ := Subtype.ext hab
      have e2 : (⟨t * v * t⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hvN)
          (Subgroup.inv_mem _ htN)⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨t, htN⟩ * ⟨v, hvN⟩ * ⟨t, htN⟩⁻¹ := rfl
      have h1 := congrArg (phiK K) (e2.symm.trans e1)
      rw [map_mul, map_mul, map_inv, map_mul, phiK_eq_one_of_mem_centralizer hqQ haK haN,
        one_mul, phiK_of_mem K ⟨t, htK⟩, hsv'] at h1
      rw [map_mul, map_mul, map_inv]
      exact h1.symm
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · exact key x hx s
    · intro h
      have := key x⁻¹ (Pb.inv_mem hx) _ h
      simpa [mul_assoc] using this
  ·
    obtain ⟨R, hRT, hRi, hR⟩ := C.exists_index_two
    replace hRi : R.relIndex Tp ≤ 2 := hRi
    set R' : Subgroup (KBar K) := ((R ⊓ K).subgroupOf K).map (piK K) with hR'
    have hR'P : R' ≤ Pb := Subgroup.map_mono (fun x hx => ⟨hRT hx.1, hx.2⟩)
    have hR'C : R' ≤ Subgroup.centralizer (E : Set (KBar K)) := by
      rintro _ ⟨⟨r, hrK⟩, hr, rfl⟩
      replace hr : r ∈ R ⊓ K := hr
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨v, hv, hvN, hsv'⟩ := (hmemE s).mp hs
      have hrN : r ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hrK
      have ha := hR r hr.1 v hv
      set a := r * v * r⁻¹ * v⁻¹ with hadef
      have haK : a ∈ Subgroup.centralizer (K : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun k hk =>
          (Subgroup.mem_centralizer_iff.mp (C.hHG (hK.1 hk)) a ha).symm
      have haN : a ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.centralizer_le_normalizer _ haK
      have e1 : (⟨r, hrN⟩ * ⟨v, hvN⟩ * ⟨r, hrN⟩⁻¹ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨a, haN⟩ * ⟨v, hvN⟩ := Subtype.ext (by
        change r * v * r⁻¹ = r * v * r⁻¹ * v⁻¹ * v
        group)
      have h1 := congrArg (phiK K) e1
      rw [map_mul, map_mul, map_inv, map_mul, phiK_eq_one_of_mem_centralizer hqQ haK haN,
        one_mul, phiK_of_mem K ⟨r, hrK⟩, hsv'] at h1
      have h2 : MulAut.conj (piK K ⟨r, hrK⟩ * s * (piK K ⟨r, hrK⟩)⁻¹) = MulAut.conj s := by
        rw [map_mul, map_mul, map_inv]
        exact h1
      have h3 := hconj h2
      calc s * piK K ⟨r, hrK⟩ = (piK K ⟨r, hrK⟩ * s * (piK K ⟨r, hrK⟩)⁻¹) * piK K ⟨r, hrK⟩ := by
            rw [h3]
        _ = piK K ⟨r, hrK⟩ * s := by group
    have h1 : (Pb ⊓ Subgroup.centralizer (E : Set (KBar K))).relIndex Pb ≤ R'.relIndex Pb :=
      Subgroup.relIndex_le_of_le_left (le_inf hR'P hR'C)
        (Subgroup.index_ne_zero_of_finite (H := R'.subgroupOf Pb))
    have h2 : R'.relIndex Pb ≤ ((R ⊓ K).subgroupOf K).relIndex (TK.subgroupOf K) :=
      relIndex_map_le_of_finite _ _ _
    have h3 : ((R ⊓ K).subgroupOf K).relIndex (TK.subgroupOf K) = (R ⊓ K).relIndex TK :=
      Subgroup.relIndex_subgroupOf (inf_le_right : TK ≤ K)
    have h4 : (R ⊓ K).relIndex TK ≤ R.relIndex Tp := by
      have e1 : (R ⊓ K).relIndex TK = R.relIndex TK := by
        rw [← Subgroup.inf_relIndex_right (R ⊓ K) TK, ← Subgroup.inf_relIndex_right R TK]
        congr 1
        rw [hTK]
        ext x
        simp only [Subgroup.mem_inf]
        tauto
      rw [e1]
      exact Subgroup.relIndex_le_of_le_right inf_le_left
        (Subgroup.index_ne_zero_of_finite (H := R.subgroupOf Tp))
    omega

theorem false_of_isComponentIn (h3108 : Stmt3_2_10_eight) (h443 : Stmt4_4_3Orbit')
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h755 : Input7_5_5) (kf1 : OutTwoNilpotentFact)
    (h23 : A23SQTKListFact) (hA23 : A23FourCentralFact) (hmult : LieMultiplierFact)
    (hcart : LieCartanFact) (hthom : LieThompsonFact) {K : Subgroup G} (hK : IsComponentIn K H) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hqQ : CFSG.IsQuasisimple (KQ K) := isQuasisimple_KQ hq
  have hvmN := C.vm_le_normalizer h37c h38c hK
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTp
  set TK := Tp ⊓ K with hTK
  have hTKs : IsSylowTwoOf TK K :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal C.sylH hK.1 hK.2.2
  set Pb : Subgroup (KBar K) := (TK.subgroupOf K).map (piK K) with hPb
  have hPbs : IsSylowTwoOf Pb ⊤ :=
    isSylowTwoOf_map_top (piK K) (piK_surjective K) (isSylowTwoOf_subgroupOf_top hTKs)
  obtain ⟨E, hEP, hEel, hEcard, hPN, hidx, hsv, hvs⟩ :=
    C.exists_E h3108 h755 h37c h38c kf1 h23 hK
  obtain ⟨hs, hnab⟩ := isSimpleGroup_KBar hqQ
  have hlist := C.a23List_KBar h23 hK hqQ
  obtain ⟨hLie, hEZ⟩ := hA23 (KBar K) hs hnab hlist Pb E hPbs hEP hEel hEcard hPN hidx
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_lie hmult hK C.oddCoreIn_eq_bot hLie hPbs hEP hEel hEcard hEZ
  have hinj : Function.Injective (piK K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_piK hq, hZ]
  set eK : ↥K ≃* KBar K := MulEquiv.ofBijective (piK K) ⟨hinj, piK_surjective K⟩ with heK
  have hsK : IsSimpleGroup ↥K := by
    have := hs
    exact eK.isSimpleGroup
  have hLieK : IsLieChar2Big ↥K := isLieChar2Big_of_mulEquiv eK hLie
  set E' : Subgroup ↥K := E.comap (piK K) with hE'
  have hrel1 : ∀ v ∈ S.vm e, ∃ k : ↥K, k ∈ E' ∧
      ((k : G))⁻¹ * v ∈ Subgroup.centralizer (K : Set G) := by
    intro v hv
    obtain ⟨s', hsE, hφ⟩ := hsv v hv
    obtain ⟨k, rfl⟩ := piK_surjective K s'
    refine ⟨k, hsE, ?_⟩
    have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
    have h1 : phiK K ⟨(k : G)⁻¹ * v, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) (hvmN hv)⟩ =
        1 := by
      have e1 : (⟨(k : G)⁻¹ * v, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) (hvmN hv)⟩ :
          ↥(Subgroup.normalizer (K : Set G))) = ⟨k, hkN⟩⁻¹ * ⟨v, hvmN hv⟩ := rfl
      rw [e1, map_mul, map_inv, phiK_of_mem K k, hφ, inv_mul_cancel]
    exact mem_centralizer_of_phiK_eq_one hq _ h1
  have hrel2 : ∀ k : ↥K, k ∈ E' → ∃ v ∈ S.vm e,
      ((k : G))⁻¹ * v ∈ Subgroup.centralizer (K : Set G) := by
    intro k hk
    obtain ⟨v, hv, hvN, hφ⟩ := hvs (piK K k) hk
    refine ⟨v, hv, ?_⟩
    have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
    have h1 : phiK K ⟨(k : G)⁻¹ * v, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hvN⟩ = 1 := by
      have e1 : (⟨(k : G)⁻¹ * v, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hvN⟩ :
          ↥(Subgroup.normalizer (K : Set G))) = ⟨k, hkN⟩⁻¹ * ⟨v, hvN⟩ := rfl
      rw [e1, map_mul, map_inv, phiK_of_mem K k, hφ, inv_mul_cancel]
    exact mem_centralizer_of_phiK_eq_one hq _ h1
  set P' : Subgroup ↥K := TK.subgroupOf K with hP'
  have hE'P' : E' ≤ P' := by
    intro k hk
    obtain ⟨t, ht, htk⟩ := hEP hk
    rw [← hinj htk]
    exact ht
  have hE'Z : E' ≤ Subgroup.centralizer (P' : Set ↥K) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp (hEZ hk) _ ⟨t, ht, rfl⟩
  have hE'el : IsElemAbelian 2 E' := isElemAbelian_comap hinj hEel
  have hE'card : Nat.card E' = 16 := by
    rw [← hEcard, ← Subgroup.card_map_of_injective hinj, hE',
      Subgroup.map_comap_eq_self_of_surjective (piK_surjective K)]
  have hTKvm : ∀ t ∈ TK, t ∈ Subgroup.centralizer (S.vm e : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨k, hk, hc⟩ := hrel1 v hv
    have h1 : (k : G) * t = t * k := by
      have := Subgroup.mem_centralizer_iff.mp (hE'Z hk) ⟨t, ht.2⟩ (show _ ∈ P' from ht)
      exact (congrArg Subtype.val this).symm
    have h2 := Subgroup.mem_centralizer_iff.mp hc t ht.2
    calc v * t = k * ((k : G)⁻¹ * v) * t := by group
      _ = k * (t * ((k : G)⁻¹ * v)) := by rw [mul_assoc, h2.symm]
      _ = (k * t) * ((k : G)⁻¹ * v) := by group
      _ = t * k * ((k : G)⁻¹ * v) := by rw [h1]
      _ = t * v := by group
  have hTKQ : TK ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := fun t ht =>
    ⟨ht.1.1, C.mem_centralizer_V ht.1.2 (hTKvm t ht)⟩
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQ
  have hQTp : Q ≤ Tp := inf_le_inf_left _ (Subgroup.centralizer_le
    (SetLike.coe_subset_coe.mpr C.vp_le_V))
  have hQK : Q ⊓ K = TK := le_antisymm (inf_le_inf_right _ hQTp) (le_inf hTKQ inf_le_right)
  have hP's : IsSylowTwoOf P' ⊤ := isSylowTwoOf_subgroupOf_top hTKs
  set B' : Subgroup ↥K := Subgroup.normalizer (P' : Set ↥K) with hB'
  have hP'B' : P' ≤ B' := Subgroup.le_normalizer
  have hN₀ : (P'.subgroupOf B').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP'B').mpr le_rfl
  have hoddB : Odd (P'.relIndex B') := by
    have h1 := Subgroup.relIndex_mul_relIndex P' B' ⊤ hP'B' le_top
    have h2 : ¬ 2 ∣ P'.relIndex ⊤ := hP's.2.2
    rw [← h1] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => h2 (Dvd.dvd.mul_right h _))
  obtain ⟨a₀, ha₀⟩ := (IsPGroup.iff_card (p := 2)).mp hP's.2.1
  have hcop : Nat.Coprime (Nat.card (P'.subgroupOf B')) (P'.subgroupOf B').index := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'B').toEquiv, ha₀]
    exact Nat.Coprime.pow_left a₀ (Nat.coprime_two_left.mpr hoddB)
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set Y' : Subgroup ↥K := H'.map B'.subtype with hY'
  have hY'B' : Y' ≤ B' := Subgroup.map_subtype_le H'
  have hY'card : Nat.card Y' = Nat.card H' := Subgroup.card_map_of_injective B'.subtype_injective
  have hcardH : Nat.card (P'.subgroupOf B') * Nat.card H' = Nat.card B' := hH'.card_mul_card
  have hcardP : Nat.card (P'.subgroupOf B') = Nat.card P' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'B').toEquiv
  have hY'odd : Odd (Nat.card Y') := by
    have h1 := (P'.subgroupOf B').card_mul_index
    rw [hY'card]
    have h2 : Nat.card H' = (P'.subgroupOf B').index := by
      have hpos : 0 < Nat.card (P'.subgroupOf B') := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (hcardH.trans h1.symm)
    rw [h2]
    exact hoddB
  have hY'mul : Nat.card Y' * Nat.card P' = Nat.card B' := by
    rw [hY'card, ← hcardP, mul_comm]
    exact hcardH
  obtain ⟨hYab, hYidx, hYdich⟩ := hcart ↥K hsK hLieK P' Y' E' hP's hY'B' hY'odd hY'mul hE'P'
    hE'el hE'card hE'Z
  set Y : Subgroup G := Y'.map K.subtype with hY
  have hYK : Y ≤ K := Subgroup.map_subtype_le Y'
  have hYodd : Odd (Nat.card Y) := by
    rw [hY, Subgroup.card_map_of_injective K.subtype_injective]
    exact hY'odd
  have hYab' : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hYab a ha b hb)
  have hcent : ∀ y : ↥K, (y : G) ∈ Subgroup.centralizer (fsuV T I : Set G) ↔
      y ∈ Subgroup.centralizer (E' : Set ↥K) := by
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      obtain ⟨v, hv, hc⟩ := hrel2 k hk
      apply Subtype.ext
      have h1 : v * (y : G) = y * v := Subgroup.mem_centralizer_iff.mp hy v (vm_le hv)
      have h2 : (y : G) * ((k : G)⁻¹ * v) = ((k : G)⁻¹ * v) * y :=
        Subgroup.mem_centralizer_iff.mp hc y y.2
      have hc' : ((k : G)⁻¹ * v)⁻¹ * y = y * ((k : G)⁻¹ * v)⁻¹ := by
        calc ((k : G)⁻¹ * v)⁻¹ * y = ((k : G)⁻¹ * v)⁻¹ * (y * ((k : G)⁻¹ * v)) *
              ((k : G)⁻¹ * v)⁻¹ := by group
          _ = ((k : G)⁻¹ * v)⁻¹ * (((k : G)⁻¹ * v) * y) * ((k : G)⁻¹ * v)⁻¹ := by rw [h2]
          _ = y * ((k : G)⁻¹ * v)⁻¹ := by group
      change (k : G) * y = y * k
      calc (k : G) * y = v * (((k : G)⁻¹ * v)⁻¹ * y) := by group
        _ = v * (y * ((k : G)⁻¹ * v)⁻¹) := by rw [hc']
        _ = (v * y) * ((k : G)⁻¹ * v)⁻¹ := by group
        _ = (y * v) * ((k : G)⁻¹ * v)⁻¹ := by rw [h1]
        _ = y * k := by group
    · intro hy
      refine C.mem_centralizer_V ?_ ?_
      · exact C.hHG (hK.1 y.2)
      · rw [Subgroup.mem_centralizer_iff]
        intro v hv
        obtain ⟨k, hk, hc⟩ := hrel1 v hv
        have h1 : (k : G) * y = y * k := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy k hk)
        have h2 := Subgroup.mem_centralizer_iff.mp hc y y.2
        calc v * y = k * ((k : G)⁻¹ * v) * y := by group
          _ = k * (y * ((k : G)⁻¹ * v)) := by rw [mul_assoc, h2.symm]
          _ = (k * y) * ((k : G)⁻¹ * v) := by group
          _ = y * k * ((k : G)⁻¹ * v) := by rw [h1]
          _ = y * v := by group
  have hYV : Y ⊓ Subgroup.centralizer (fsuV T I : Set G) =
      (Y' ⊓ Subgroup.centralizer (E' : Set ↥K)).map K.subtype := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxV⟩
      exact ⟨y, ⟨hy, (hcent y).mp hxV⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyE⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, (hcent y).mpr hyE⟩
  have hYidx' : 3 < (Y ⊓ Subgroup.centralizer (fsuV T I : Set G)).relIndex Y := by
    rw [hYV, hY, Subgroup.relIndex_map_map_of_injective _ _ K.subtype_injective]
    exact hYidx
  have hYz : Y ≤ Subgroup.centralizer ({S.vec e a1} : Set G) :=
    (hYK.trans (hK.1.trans C.hHG)).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr C.z_mem))
  have hfin : ¬ Y ≤ fsuM T L := fun hYM => by
    have := S.relIndex_le_three hYM hYodd (vec_mem a1) vec_a1_ne_one hYz
    omega
  apply hfin
  by_cases hY0 : Y' ⊓ Subgroup.centralizer (E' : Set ↥K) = ⊥
  ·
    have hLtype := hYdich hY0
    have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple
      S.hyp.fsu.nonabelian C.pCoreOf_ne_bot
    have hcomp : K ∈ cComp H := Vol2Native.mem_cComp_of_isComponentIn hK
    have hA3 : A3Orbits G := a3Orbits_of_a37_a38 h37 h38
    obtain ⟨-, hcases⟩ := hA3 H Tp K hSQ C.sylH hcomp
    obtain ⟨K', hK'c, hQN⟩ : ∃ K' : Subgroup G, (K' = K ∨ ∃ r ∈ Q, K' = CFSG.conjugate K r ∧
        ⁅K, K'⁆ = ⊥) ∧ Q ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := by
      by_cases hQK' : Q ≤ Subgroup.normalizer (K : Set G)
      · exact ⟨K, Or.inl rfl, by rwa [sup_idem]⟩
      · rcases hcases with hnorm | ⟨t, -, -, hpair, -, -, hTKK⟩
        · exact absurd (fun q hq => hnorm q (hQTp hq)) hQK'
        · obtain ⟨r, hrQ, hrN⟩ : ∃ r ∈ Q, r ∉ Subgroup.normalizer (K : Set G) := by
            by_contra hcon
            push Not at hcon
            exact hQK' hcon
          have hrH : r ∈ H := C.tp_le_H (hQTp hrQ)
          have hmem : CFSG.conjugate K r ∈ conjSubgroupsBy Tp K :=
            ⟨r⁻¹, Tp.inv_mem (hQTp hrQ), rfl⟩
          rw [hpair] at hmem
          have hne : CFSG.conjugate K r ≠ K := by
            intro h
            apply hrN
            have h1 : r⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
              Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
            simpa using Subgroup.inv_mem _ h1
          rcases hmem with h1 | h1
          · exact absurd h1 hne
          · have h1' : CFSG.conjugate K r = conjByElt t K := h1
            refine ⟨CFSG.conjugate K r, Or.inr ⟨r, hrQ, rfl, ?_⟩, ?_⟩
            · exact (BenderBranch.eq_or_commute_of_isComponentIn hK
                (Unc25G2.isComponentIn_conjugate hK hrH)).resolve_left (Ne.symm hne)
            · rw [h1']
              exact hQTp.trans hTKK
    have hQ2 : IsPGroup 2 ↥Q := S.hyp.fsu.sylow.1.to_le inf_le_left
    have hQKs : IsSylowTwoOf (Q ⊓ K) K := hQK ▸ hTKs
    have hEQ : ∃ E₀ : Subgroup G, E₀ ≤ Q ⊓ K ∧ IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 16 ∧
        E₀ ≤ Subgroup.centralizer ((Q ⊓ K : Subgroup G) : Set G) := by
      refine ⟨E'.map K.subtype, ?_, isElemAbelian_map _ hE'el, ?_, ?_⟩
      · rw [hQK]
        rintro _ ⟨k, hk, rfl⟩
        exact (hE'P' hk : k ∈ P')
      · rw [Subgroup.card_map_of_injective K.subtype_injective, hE'card]
      · rintro _ ⟨k, hk, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [hQK] at ht
        have := Subgroup.mem_centralizer_iff.mp (hE'Z hk) ⟨t, ht.2⟩ (show _ ∈ P' from ht)
        exact congrArg Subtype.val this
    have hJ' := hthom G K K' Q hsK hLtype hQ2 hK'c hQN hQKs hEQ
    set X := ((Q ⊓ K) ⊔ (Q ⊓ K')) ⊔
      (Q ⊓ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G)) with hX
    have hXQ : X ≤ Q := sup_le (sup_le inf_le_left inf_le_left) inf_le_left
    have hX2 : IsPGroup 2 ↥X := hQ2.to_le hXQ
    have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
    have hJQ : thompsonJ T ≤ Q := le_inf hJT S.hJ
    have hJX : thompsonJ T ≤ X := by
      refine iSup₂_le fun A hA => hJ' A ⟨?_, hA.2.1,
        fun B hBQ hB => hA.2.2 B (hBQ.trans inf_le_left) hB⟩
      exact (le_iSup₂ (f := fun A (_ : IsMaxElemAbelian T A) => A) A hA).trans hJQ
    have hVp : IsVplus T L I (fsuV T I) := Or.inr ⟨fun h => h.1 S.hL, rfl⟩
    have hNX := (h3108 G T L I (fsuV T I) S.hyp.fsu hVp S.hJ X hX2 hJX).2
    refine le_trans ?_ hNX
    rintro _ ⟨y, hy, rfl⟩
    have hyN : (y : G) ∈ Subgroup.normalizer (TK : Set G) := by
      have h1 : y ∈ B' := hY'B' hy
      rw [hB', ← Subgroup.subgroupOf_normalizer_eq (inf_le_right : TK ≤ K)] at h1
      exact h1
    have h1 : (Q ⊓ K).map (MulAut.conj (y : G)).toMonoidHom = Q ⊓ K := by
      rw [hQK]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN
    have h2 : (Q ⊓ K').map (MulAut.conj (y : G)).toMonoidHom = Q ⊓ K' := by
      rcases hK'c with rfl | ⟨r, -, -, hcomm⟩
      · exact h1
      · refine map_conj_eq_of_commute fun a ha => ?_
        exact (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm y.2) a ha.2).symm
    have h3 : (Q ⊓ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G)).map
        (MulAut.conj (y : G)).toMonoidHom =
        Q ⊓ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G) := by
      refine map_conj_eq_of_commute fun a ha => ?_
      exact Subgroup.mem_centralizer_iff.mp ha.2 y (Subgroup.mem_sup_left y.2)
    have hfinal : X.map (MulAut.conj (y : G)).toMonoidHom = X := by
      rw [hX, Subgroup.map_sup, Subgroup.map_sup, h1, h2, h3]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfinal
  ·
    set B₀ := Y ⊓ Subgroup.centralizer (fsuV T I : Set G) with hB₀
    have hB₀1 : B₀ ≠ ⊥ := by
      rw [hYV]
      intro h
      apply hY0
      rw [Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h
      exact h
    have hB₀c : IsMulCommutative ↥B₀ :=
      ⟨⟨fun a b => Subtype.ext (hYab' a a.2.1 b b.2.1)⟩⟩
    have hB₀o : Odd (Nat.card B₀) :=
      Odd.of_dvd_nat hYodd (Subgroup.card_dvd_of_le inf_le_left)
    have hNB := S.normalizer_le h443 (inf_le_right.trans S.centralizer_le_fsuM) inf_le_right
      hB₀1 hB₀c hB₀o
    refine le_trans ?_ hNB
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h1 := hYab' y hy b hb.1
      rw [h1, mul_inv_cancel_right]
      exact hb
    · intro hb
      have hbY : b ∈ Y := by
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hb.1) hy
        simpa [mul_assoc] using this
      have h1 := hYab' y hy b hbY
      rwa [h1, mul_inv_cancel_right] at hb

theorem charTwo (h3108 : Stmt3_2_10_eight) (h443 : Stmt4_4_3Orbit') (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h755 : Input7_5_5) (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact)
    (hA23 : A23FourCentralFact) (hmult : LieMultiplierFact) (hcart : LieCartanFact)
    (hthom : LieThompsonFact) : CharTwo H :=
  DoubleA3.charTwo_of_no_component
    (fun _ hK => C.false_of_isComponentIn h3108 h443 h37 h38 h37c h38c h755 kf1 h23 hA23 hmult
      hcart hthom hK)
    C.oddCoreIn_eq_bot

end Conf

end Setup

end CFSG.Quasithin.H13.Sec77
