module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModP
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7ModO

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem normalizer_sup' {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) :
      Set G) := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => le_sup_left (a := A) ((Subgroup.mem_normalizer_iff.1 hA a).1 ha))
      (fun b hb => le_sup_right (b := B) ((Subgroup.mem_normalizer_iff.1 hB b).1 hb))
  exact normalizer_of_maps fun w hw => hle hw

theorem two6_of_pow2 {W : Type} [CommGroup W] (C : Coding W)
    {a : MulAut W} (ha : C.cB a ∈ gm6) {k : ℕ} (hk : a ^ 2 ^ k = 1) : two6 (C.cB a) = true := by
  have hp : IsPGroup 2 (Subgroup.zpowers a) := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk
  exact pow_four_of_isPGroup C hp (Subgroup.mem_zpowers a) ha

variable {T L V : Subgroup G}

omit [Finite G] in
theorem conj_mem_centralizer {g c : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) v).1 hv
    simpa using this
  have := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * v := by group

theorem normalizer_oTwoZIn (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (oTwoZIn L : Set G) := by
  apply normalizer_of_maps
  intro x hx
  obtain ⟨hxL, hxc⟩ := (mem_oTwoZIn h1222 h).1 hx
  refine (mem_oTwoZIn h1222 h).2 ⟨(Subgroup.mem_normalizer_iff.1 hgL x).1 hxL, fun m hm => ?_⟩
  have hm' : g⁻¹ * m * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgL) m).1 hm
    simpa using this
  have hc := conj_mem_centralizer hgV (hxc _ hm')
  have e : (g * x * g⁻¹)⁻¹ * m⁻¹ * (g * x * g⁻¹) * m =
      g * (x⁻¹ * (g⁻¹ * m * g)⁻¹ * x * (g⁻¹ * m * g)) * g⁻¹ := by group
  rw [e]
  exact hc

theorem normalizer_XOf (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (XOf L : Set G) :=
  normalizer_le_normalizer_oTwoUpper _ (normalizer_oTwoZIn h1222 h hgL hgV)

theorem pof_le_normalizer_L (h : Hyp1271 G T L V) (W : Subgroup G) :
    Pof T L W ≤ Subgroup.normalizer (L : Set G) :=
  inf_le_left.trans (sup_le Subgroup.le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer
      h.hyp.normalizes)))

omit [Finite G] in
theorem pCoreOf_normal' (I : Subgroup G) : ((pCoreOf 2 I).subgroupOf I).Normal := by
  have e : (pCoreOf 2 I).subgroupOf I = CFSG.Open.pCore 2 ↥I := by
    show (Subgroup.map I.subtype (CFSG.Open.pCore 2 ↥I)).comap I.subtype = _
    exact Subgroup.comap_map_eq_self_of_injective I.subtype_injective _
  rw [e]
  exact CFSG.LieType.BorelTits.pCore_normal 2

theorem pCoreOf_le_T (h : Hyp1271 G T L V) {J : Subgroup G}
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) : pCoreOf 2 J ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_of_isPGroup_of_le_normalizer h.hyp.sylow
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (hTJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))

theorem eq_of_lift (h : Hyp1271 G T L V) {P I J : Subgroup G}
    (hKP : IsPGroup 2 (P ⊓ Subgroup.centralizer (V : Set G) : Subgroup G))
    (hPJ : P ≤ Subgroup.normalizer (J : Set G))
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) (hJO : oTwoUpper J = J)
    (hJ3 : (pCoreOf 2 J).relIndex J = 3) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    (hIO : oTwoUpper I = I) {y : G} (hyI : y ∈ I) (hy3 : orderOf y = 3)
    (hlift : ∀ i ∈ I, ∃ x ∈ J, x⁻¹ * i ∈ P ⊓ Subgroup.centralizer (V : Set G)) : I = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIJ : I ≤ J := by
    rw [← hIO]
    apply oTwoUpper_le_of_pow
    intro i hi
    obtain ⟨x, hxJ, hc⟩ := hlift i hi
    obtain ⟨k, hk⟩ := pow_mem_of_mul hKP (fun c hc' => hPJ (Subgroup.mem_inf.1 hc').1) hxJ hc
    exact ⟨k, by simpa using hk⟩
  refine le_antisymm hIJ ?_
  rw [← hJO]
  apply oTwoUpper_le_of_pow
  intro j hj
  have hNn := pCoreOf_normal' J
  obtain ⟨k, hk⟩ := idx3_coset (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hJ3 (hIJ hyI)
    hy3 hj
  set u := j * (y ^ k)⁻¹ with hu
  have huT : u ∈ T := pCoreOf_le_T h hTJ hk
  have hn : u * y ^ k * u⁻¹ ∈ I :=
    (Subgroup.mem_normalizer_iff.1 (hTI huT) _).1 (I.pow_mem hyI k)
  have hKI : pCoreOf 2 J ≤ Subgroup.normalizer (I : Set G) :=
    fun c hc => hTI (pCoreOf_le_T h hTJ hc)
  obtain ⟨m, hm⟩ := pow_mem_of_mul (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hKI hn hk
  refine ⟨m, ?_⟩
  have e : u * y ^ k * u⁻¹ * u = j := by rw [hu]; group
  rw [e] at hm
  exact hm

variable [IsMulCommutative ↥V]

open Classical in
@[expose] noncomputable def Coding.gc (C : Coding ↥V) (x : G) : B6 :=
  if hx : x ∈ Subgroup.normalizer (V : Set G) then C.cB (conjAct V ⟨x, hx⟩) else B6.id

omit [Finite G] in
theorem Coding.gc_of (C : Coding ↥V) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    C.gc x = C.cB (conjAct V ⟨x, hx⟩) := by
  simp [Coding.gc, hx]

omit [Finite G] in
theorem Coding.gc_mul (C : Coding ↥V) {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) : C.gc (x * y) = (C.gc x).comp (C.gc y) := by
  rw [C.gc_of hx, C.gc_of hy, C.gc_of (Subgroup.mul_mem _ hx hy), conjAct_mul' hx hy, C.cB_mul]

omit [Finite G] in
theorem Coding.gc_pow (C : Coding ↥V) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (n : ℕ) : C.gc (x ^ n) = (C.gc x).pow n := by
  rw [C.gc_of hx, C.gc_of (Subgroup.pow_mem _ hx n), ← C.cB_pow, ← map_pow]
  rfl

omit [Finite G] in
theorem Coding.gc_inv (C : Coding ↥V) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hg : C.gc x ∈ gm6) :
    C.gc x⁻¹ = inv6 (C.gc x) := by
  rw [C.gc_of hx] at hg ⊢
  rw [C.gc_of (Subgroup.inv_mem _ hx), ← cB_inv_eq C hg, ← map_inv]
  rfl

omit [Finite G] in
theorem Coding.gc_eq_id (C : Coding ↥V) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    C.gc x = B6.id ↔ x ∈ Subgroup.centralizer (V : Set G) := by
  rw [C.gc_of hx, C.cB_eq_one, conjAct_eq_one']

omit [Finite G] [IsMulCommutative ↥V] in
theorem inv_mul_mem_of_conj_eq {P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (V : Set G))
    {x y : G} (hx : x ∈ P) (hy : y ∈ P)
    (he : conjAct V ⟨x, hPN hx⟩ = conjAct V ⟨y, hPN hy⟩) :
    x⁻¹ * y ∈ P ⊓ Subgroup.centralizer (V : Set G) := by
  have hN : x⁻¹ * y ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _
    (Subgroup.inv_mem _ (hPN hx)) (hPN hy)
  refine Subgroup.mem_inf.2 ⟨P.mul_mem (P.inv_mem hx) hy, (conjAct_eq_one' hN).1 ?_⟩
  have e : conjAct V ⟨x⁻¹ * y, hN⟩ = (conjAct V ⟨x, hPN hx⟩)⁻¹ * conjAct V ⟨y, hPN hy⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [e, he, inv_mul_cancel]

theorem five_generic
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L)
    {W : Subgroup G} {l : List ℕ} {lc : List B6} {Li : Subgroup G}
    (hP : ∀ a, a ∈ autOn (Pof T L W) V ↔ C.cB a ∈ gm6 ∧ presv l (C.cB a) = true)
    (hLi : ∀ a, a ∈ autOn Li V ↔ C.cB a ∈ lc) (hlc : ∀ B ∈ lc, B ∈ gm6)
    (hlc1 : B6.id ∈ lc) (hlccl : ∀ x ∈ lc, ∀ y ∈ lc, x.comp y ∈ lc)
    (hLiP : Li ≤ Pof T L W) (hTLi : T ≤ Subgroup.normalizer (Li : Set G))
    (hPLi : Pof T L W ≤ Subgroup.normalizer (Li : Set G)) (hLiO : oTwoUpper Li = Li)
    (hLi3 : (pCoreOf 2 Li).relIndex Li = 3) (hXP : XOf L ≤ Pof T L W)
    (hX3 : (pCoreOf 2 (XOf L)).relIndex (XOf L) = 3)
    (hord3 : ∀ y ∈ gm6, presv l y = true → ord3 y = true → y ∈ zs6 ∨ y ∈ lc ∨
      ∃ s ∈ s0, two6 (y.comp (inv6 ((s.comp y).comp (inv6 s)))) = false ∧
        two6 (y.comp ((s.comp y).comp (inv6 s))) = false)
    (hbeta : ∀ u ∈ gm6, presv l u = true → two6 u = true → u ∉ lc → ∀ y ∈ lc, ord3 y = true →
      two6 (u.comp ((y.comp u).comp (inv6 y))) = false ∨
        two6 (u.comp (((inv6 y).comp u).comp y)) = false)
    (hsq : ∀ g ∈ gm6, presv l g = true → ∃ a ∈ lc, ∃ z ∈ zs6, g.comp g = a.comp z) :
    oTwoUpper (Pof T L W) = Li ⊔ XOf L ∧
      {I : Subgroup G | I ≤ Pof T L W ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
        oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} = {Li, XOf L} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Pof T L W with hPdef
  set X := XOf L with hXdef
  have hPN := pof_le_normalizer h1222 h W
  have hK2 := pof_inf_centralizer_isPGroup h1222 h W
  have hX := mem_autOn_XOf h1222 h hC.1
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := fun g hg =>
    normalizer_XOf h1222 h (pof_le_normalizer_L h W hg) (hPN hg)
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun g hg =>
    normalizer_XOf h1222 h (h.hyp.normalizes hg) (T_le_normalizer h1222 h hg)
  have hXO : oTwoUpper X = X := oTwoUpper_idem _
  have hKN : ∀ {J : Subgroup G}, P ≤ Subgroup.normalizer (J : Set G) →
      P ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    fun hPJ _ hc => hPJ (Subgroup.mem_inf.1 hc).1
  have hlift : ∀ {J : Subgroup G} {lJ : List B6}, (∀ a, a ∈ autOn J V ↔ C.cB a ∈ lJ) →
      (∀ B ∈ lJ, B ∈ gm6) → J ≤ P → ∀ i (hi : i ∈ P), C.cB (conjAct V ⟨i, hPN hi⟩) ∈ lJ →
        ∃ x ∈ J, x⁻¹ * i ∈ P ⊓ Subgroup.centralizer (V : Set G) := by
    intro J lJ hJ hlJ hJP i hi hci
    obtain ⟨a, ha⟩ := hC.1.2 _ (hlJ _ hci)
    obtain ⟨x, hxN, hxJ, hxa⟩ := mem_autOn'.1 ((hJ a).2 (ha ▸ hci))
    refine ⟨x, hxJ, inv_mul_mem_of_conj_eq hPN (hJP hxJ) hi ?_⟩
    apply C.cB_injective
    have hxa' : conjAct V ⟨x, hPN (hJP hxJ)⟩ = a := hxa
    rw [hxa', ha]
  have hcodeP : ∀ x (hx : x ∈ P), C.cB (conjAct V ⟨x, hPN hx⟩) ∈ gm6 ∧
      presv l (C.cB (conjAct V ⟨x, hPN hx⟩)) = true :=
    fun x hx => (hP _).1 (conjAct_mem_autOn hx (hPN hx))
  have h5a : oTwoUpper P = Li ⊔ X := by
    apply le_antisymm
    · apply oTwoUpper_le_of_pow
      intro g hg
      obtain ⟨hgm, hgl⟩ := hcodeP g hg
      obtain ⟨a, ha, z, hz, he⟩ := hsq _ hgm hgl
      obtain ⟨y1, hy1, hc1⟩ : ∃ y1, ∃ hy1 : y1 ∈ Li,
          C.cB (conjAct V ⟨y1, hPN (hLiP hy1)⟩) = a := by
        obtain ⟨b, rfl⟩ := hC.1.2 _ (hlc a ha)
        obtain ⟨y1, hy1N, hy1L, rfl⟩ := mem_autOn'.1 ((hLi b).2 ha)
        exact ⟨y1, hy1L, rfl⟩
      obtain ⟨y2, hy2, hc2⟩ : ∃ y2, ∃ hy2 : y2 ∈ X,
          C.cB (conjAct V ⟨y2, hPN (hXP hy2)⟩) = z := by
        obtain ⟨b, rfl⟩ := hC.1.2 _ (zs6_sub_gm6 z hz)
        obtain ⟨y2, hy2N, hy2X, rfl⟩ := mem_autOn'.1 ((hX b).2 hz)
        exact ⟨y2, hy2X, rfl⟩
      have hnP : y1 * y2 ∈ P := P.mul_mem (hLiP hy1) (hXP hy2)
      have hg2P : g ^ 2 ∈ P := P.pow_mem hg 2
      have hc : (y1 * y2)⁻¹ * g ^ 2 ∈ P ⊓ Subgroup.centralizer (V : Set G) := by
        apply inv_mul_mem_of_conj_eq hPN hnP hg2P
        apply C.cB_injective
        rw [conjAct_mul' (hPN (hLiP hy1)) (hPN (hXP hy2)), C.cB_mul, hc1, hc2, ← he]
        have e : conjAct V ⟨g ^ 2, hPN hg2P⟩ = conjAct V ⟨g, hPN hg⟩ ^ 2 := by
          rw [← map_pow]
          rfl
        rw [e, C.cB_pow]
        show _ = (C.cB (conjAct V ⟨g, hPN hg⟩)).comp ((C.cB (conjAct V ⟨g, hPN hg⟩)).comp B6.id)
        rw [B6.comp_id]
      obtain ⟨k, hk⟩ := pow_mem_of_mul hK2 (hKN fun x hx => normalizer_sup' (hPLi hx) (hPX hx))
        (Subgroup.mul_mem _ (le_sup_left (a := Li) hy1) (le_sup_right (b := X) hy2)) hc
      refine ⟨k + 1, ?_⟩
      rw [mul_inv_cancel_left] at hk
      rw [Nat.pow_succ', pow_mul]
      exact hk
    · exact sup_le (hLiO ▸ oTwoUpper_mono hLiP) (hXO ▸ oTwoUpper_mono hXP)
  refine ⟨h5a, ?_⟩
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hIP, hTI, hIO, hI3⟩
    have hNn := pCoreOf_normal' I
    have hN2 : IsPGroup 2 (pCoreOf 2 I) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    obtain ⟨y, hyI, hy3⟩ := idx3_exists hI3
    have hyP := hIP hyI
    obtain ⟨hym, hyl⟩ := hcodeP y hyP
    set gy := C.cB (conjAct V ⟨y, hPN hyP⟩) with hgy
    have hgy3 : ord3 gy = true := by
      have h3 : gy.pow 3 = B6.id := by
        rw [hgy, ← C.cB_pow, ← map_pow]
        have : (⟨y, hPN hyP⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 3 = 1 :=
          Subtype.ext (by simp [← hy3, pow_orderOf_eq_one])
        rw [this, map_one, C.cB_one]
      have hne : gy ≠ B6.id := by
        intro e
        have h1 := (conjAct_eq_one' (hPN hyP)).1 (C.cB_eq_one.1 e)
        exact not_mem_of_orderOf_three hK2 hy3 (Subgroup.mem_inf.2 ⟨hyP, h1⟩)
      simp [ord3, h3, hne]
    have htwoN : ∀ u (hu : u ∈ pCoreOf 2 I), two6 (C.cB (conjAct V ⟨u, hPN (hIP
        (CFSG.LieType.BorelTits.pCoreOf_le 2 I hu))⟩)) = true := by
      intro u hu
      obtain ⟨k, hk⟩ := hN2 ⟨u, hu⟩
      have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine two6_of_pow2 C (hcodeP u (hIP (CFSG.LieType.BorelTits.pCoreOf_le 2 I hu))).1
        (k := k) ?_
      rw [← map_pow]
      have : (⟨u, hPN (hIP (CFSG.LieType.BorelTits.pCoreOf_le 2 I hu))⟩ :
          ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 := Subtype.ext (by simp [hk'])
      rw [this, map_one]
    have hcI : ∀ {i : G} (hi : i ∈ I), C.gc i ∈ gm6 := fun hi => by
      rw [C.gc_of (hPN (hIP hi))]
      exact (hcodeP _ (hIP hi)).1
    have hNI : ∀ {i : G}, i ∈ I → i ∈ Subgroup.normalizer (V : Set G) := fun hi => hPN (hIP hi)
    have hgyc : C.gc y = gy := C.gc_of (hNI hyI)
    have hNnI : I ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I
    have hNle : pCoreOf 2 I ≤ I := CFSG.LieType.BorelTits.pCoreOf_le 2 I
    have htwo' : ∀ {u : G}, u ∈ pCoreOf 2 I → two6 (C.gc u) = true := fun hu => by
      rw [C.gc_of (hNI (hNle hu))]
      exact htwoN _ hu
    rcases hord3 gy hym hyl hgy3 with hz | hlcy | ⟨s, hs, hs1, hs2⟩
    ·
      right
      have hZ1 : B6.id ∈ zs6 := by decide
      have hZc : ∀ x ∈ zs6, ∀ y ∈ zs6, x.comp y ∈ zs6 := by decide
      set Zs := C.subOf zs6 hZ1 hZc with hZs
      have hcyZ : conjAct V ⟨y, hPN hyP⟩ ∈ Zs := hz
      have hIZ : autOn I V ≤ Zs := by
        rw [← hIO, autOn_oTwoUpper (hIP.trans hPN), oTwoUpper, Subgroup.closure_le]
        rintro w ⟨hw, hwodd⟩
        obtain ⟨i, hiN, hiO, rfl⟩ := mem_autOn'.1 hw
        have hiI : i ∈ I := hiO
        obtain ⟨k, hk⟩ := idx3_coset hN2 hI3 hyI hy3 hiI
        set u := i * (y ^ k)⁻¹ with hu
        have huN := hNI (hNle hk)
        set ci := conjAct V ⟨i, hiN⟩ with hci
        set cy := conjAct V ⟨y, hPN hyP⟩ with hcy
        set cu := conjAct V ⟨u, huN⟩ with hcu
        have ecu : cu = ci * (cy ^ k)⁻¹ := by
          rw [hcu, hci, hcy, ← map_pow, ← map_inv, ← map_mul]
          rfl
        have hcomm : ci * cy = cy * ci := by
          apply C.cB_injective
          rw [C.cB_mul, C.cB_mul]
          exact (zs6_comm _ hz _ (by rw [hci, ← C.gc_of hiN]; exact hcI hiI)).symm
        obtain ⟨j, hj⟩ := hN2 ⟨u, hk⟩
        have hj' : u ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
        have hcuj : cu ^ 2 ^ j = 1 := by
          rw [hcu, ← map_pow]
          have : (⟨u, huN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ j = 1 :=
            Subtype.ext (by simp [hj'])
          rw [this, map_one]
        set m := orderOf ci with hm
        have hcum : cu ^ m ∈ Zs := by
          have hc' : Commute ci (cy ^ k)⁻¹ := ((Commute.pow_right hcomm k)).inv_right
          rw [ecu, hc'.mul_pow, hm, pow_orderOf_eq_one, one_mul]
          exact Zs.pow_mem (Zs.inv_mem (Zs.pow_mem hcyZ k)) _
        have hcop : m.Coprime (orderOf cu) :=
          Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hcuj)
            (Nat.Coprime.pow_right j (Nat.coprime_two_right.2 hwodd))
        obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime hcop
        have hcuZ : cu ∈ Zs := he ▸ Zs.pow_mem hcum e
        have eci : ci = cu * cy ^ k := by rw [ecu]; group
        rw [eci]
        exact Zs.mul_mem hcuZ (Zs.pow_mem hcyZ k)
      exact eq_of_lift h hK2 hPX hTX hXO hX3 hTI hIO hyI hy3 fun i hi =>
        hlift hX (fun B hB => zs6_sub_gm6 B hB) hXP i (hIP hi)
          (hIZ (conjAct_mem_autOn hi (hPN (hIP hi))))
    ·
      left
      have hIL : ∀ i (hi : i ∈ I), C.cB (conjAct V ⟨i, hPN (hIP hi)⟩) ∈ lc := by
        intro i hi
        obtain ⟨k, hk⟩ := idx3_coset hN2 hI3 hyI hy3 hi
        set u := i * (y ^ k)⁻¹ with hu
        have huI := hNle hk
        have hul : C.gc u ∈ lc := by
          by_contra hnot
          have hum := hcI huI
          have hupl : presv l (C.gc u) = true := by
            rw [C.gc_of (hNI huI)]
            exact (hcodeP _ (hIP huI)).2
          rcases hbeta _ hum hupl (htwo' hk) hnot gy hlcy hgy3 with h1 | h1
          · have hm : u * (y * u * y⁻¹) ∈ pCoreOf 2 I :=
              (pCoreOf 2 I).mul_mem hk ((Subgroup.mem_normalizer_iff.1 (hNnI hyI) u).1 hk)
            have h2 := htwo' hm
            rw [C.gc_mul (hNI huI) (hNI (I.mul_mem (I.mul_mem hyI huI) (I.inv_mem hyI))),
              C.gc_mul (hNI (I.mul_mem hyI huI)) (hNI (I.inv_mem hyI)),
              C.gc_mul (hNI hyI) (hNI huI), C.gc_inv (hNI hyI) (hcI hyI), hgyc] at h2
            rw [h2] at h1
            exact Bool.noConfusion h1
          · have hm : u * (y⁻¹ * u * y) ∈ pCoreOf 2 I := by
              refine (pCoreOf 2 I).mul_mem hk ?_
              have := (Subgroup.mem_normalizer_iff.1 (hNnI (I.inv_mem hyI)) u).1 hk
              simpa using this
            have h2 := htwo' hm
            rw [C.gc_mul (hNI huI) (hNI (I.mul_mem (I.mul_mem (I.inv_mem hyI) huI) hyI)),
              C.gc_mul (hNI (I.mul_mem (I.inv_mem hyI) huI)) (hNI hyI),
              C.gc_mul (hNI (I.inv_mem hyI)) (hNI huI), C.gc_inv (hNI hyI) (hcI hyI), hgyc] at h2
            rw [h2] at h1
            exact Bool.noConfusion h1
        have e : i = u * y ^ k := by rw [hu]; group
        rw [← C.gc_of, e, C.gc_mul (hNI huI) (hNI (I.pow_mem hyI k)), C.gc_pow (hNI hyI), hgyc]
        exact hlccl _ hul _ (pow_mem_of_comp_mem hlc1 hlccl hlcy k)
      exact eq_of_lift h hK2 hPLi hTLi hLiO hLi3 hTI hIO hyI hy3 fun i hi =>
        hlift hLi hlc hLiP i (hIP hi) (hIL i hi)
    ·
      exfalso
      obtain ⟨a, ha, hac⟩ := hC.s0_surj s hs
      obtain ⟨x, hxN, hxTL, rfl⟩ := mem_autOn'.1 ha
      have hxT := (Subgroup.mem_inf.1 hxTL).1
      have hy'I : x * y * x⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hTI hxT) y).1 hyI
      have hy'3 : orderOf (x * y * x⁻¹) = 3 := by rw [orderOf_conj']; exact hy3
      have hsx : C.gc x = s := by rw [C.gc_of hxN]; exact hac
      have hsgm : s ∈ gm6 := s0_sub_gm6 s hs
      have hcy' : C.gc (x * y * x⁻¹) = (s.comp gy).comp (inv6 s) := by
        rw [C.gc_mul (Subgroup.mul_mem _ hxN (hNI hyI)) (Subgroup.inv_mem _ hxN),
          C.gc_mul hxN (hNI hyI), C.gc_inv hxN (hsx ▸ hsgm), hsx, hgyc]
      rcases idx3_pair hN2 hI3 hyI hy'I hy3 hy'3 with hm | hm
      · have h2 := htwo' hm
        rw [C.gc_mul (hNI hyI) (Subgroup.inv_mem _ (hNI hy'I)), C.gc_inv (hNI hy'I) (hcI hy'I),
          hcy', hgyc] at h2
        rw [h2] at hs1
        exact Bool.noConfusion hs1
      · have h2 := htwo' hm
        rw [C.gc_mul (hNI hyI) (hNI hy'I), hcy', hgyc] at h2
        rw [h2] at hs2
        exact Bool.noConfusion hs2
  · rintro (rfl | rfl)
    · exact ⟨hLiP, hTLi, hLiO, hLi3⟩
    · exact ⟨hXP, hTX, hXO, hX3⟩

end CFSG.Quasithin.H13.S127.Mod

end
