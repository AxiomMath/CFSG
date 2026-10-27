module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UGlue2
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UGlue1
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UKNorm

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement

section Glue3

variable {G : Type} [Group G] [Finite G]

theorem ob5_O2K_le_T {T U K : Subgroup G} (hKle : K ≤ Subgroup.normalizer (U : Set G))
    (hKn : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (U : Set G))) :
    pCoreOf 2 K ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 (Subgroup.normalizer (U : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKle)
      (hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact h1.trans (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS)

theorem ob5_O2K_inter_le {I K : Subgroup G}
    (hIn : ∀ i ∈ I, ∀ q ∈ pCoreOf 2 K, i * q * i⁻¹ ∈ pCoreOf 2 K) :
    pCoreOf 2 K ⊓ I ≤ pCoreOf 2 I := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have back : ∀ i ∈ I, ∀ x : G, i * x * i⁻¹ ∈ pCoreOf 2 K → x ∈ pCoreOf 2 K := by
    intro i hi x hx
    have h1 := hIn i⁻¹ (I.inv_mem hi) _ hx
    have e : i⁻¹ * (i * x * i⁻¹) * i⁻¹⁻¹ = x := by group
    rw [e] at h1
    exact h1
  apply CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
  · intro i hi
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxQ, hxI⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hIn i hi x hxQ, I.mul_mem (I.mul_mem hi hxI) (I.inv_mem hi)⟩
    · intro hx
      obtain ⟨hxQ, hxI⟩ := Subgroup.mem_inf.mp hx
      have hxI' : x ∈ I := by
        have := I.mul_mem (I.mul_mem (I.inv_mem hi) hxI) hi
        simpa [mul_assoc] using this
      exact Subgroup.mem_inf.mpr ⟨back i hi x hxQ, hxI'⟩
  · intro g
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨g.1, (inf_le_left : pCoreOf 2 K ⊓ I ≤ pCoreOf 2 K) g.2⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩

theorem ob5_h_mem_centralizer {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (c : S828Ctx T L I H h k) :
    h ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h1 := c.hcen u hu h c.hhI
  calc u * h = h * u * h⁻¹ * h := by rw [h1]
    _ = h * u := by group

theorem ob5_Q_norm_I {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) {K : Subgroup G}
    (hKle : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))
    (hKn : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (ch82U (fsuV T I) h : Set G))) :
    ∀ q ∈ pCoreOf 2 K, ∀ i ∈ ch82I (fsuV T I) h,
      q * i * q⁻¹ ∈ ch82I (fsuV T I) h := by
  classical
  set V := fsuV T I with hVdef
  set Vh := B6.conjSub h V with hVhdef
  have hI : ch82I V h = V ⊔ Vh := rfl
  have hhN : h ∈ Subgroup.normalizer (ch82U V h : Set G) :=
    (Subgroup.centralizer_le_normalizer _) (ob5_h_mem_centralizer c)
  intro q hq i hi
  have hO2 := ob5_O2K_le_T (T := T) hKle hKn hS
  have hqT : q ∈ T := hO2 hq
  have hhK : h⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ (hKn hhN)
  have hh'q : h⁻¹ * q * h ∈ pCoreOf 2 K := by
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hhK) q).mp hq
    simpa [mul_assoc] using this
  have hh'qT : h⁻¹ * q * h ∈ T := hO2 hh'q
  have hqN : q ∈ Subgroup.normalizer (V : Set G) := c.hTV hqT
  have hh'qN : h⁻¹ * q * h ∈ Subgroup.normalizer (V : Set G) := c.hTV hh'qT
  have hV_conj : ∀ v ∈ V, q * v * q⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hqN v).mp hv
  have hVh_conj : ∀ w ∈ Vh, q * w * q⁻¹ ∈ Vh := by
    intro w hw
    rw [hVhdef, B6.mem_conjSub] at hw
    rw [hVhdef, B6.mem_conjSub]
    have hv' : (h⁻¹ * q * h) * (h⁻¹ * w * h) * (h⁻¹ * q * h)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hh'qN _).mp hw
    have e : h⁻¹ * (q * w * q⁻¹) * h = (h⁻¹ * q * h) * (h⁻¹ * w * h) * (h⁻¹ * q * h)⁻¹ := by
      group
    rw [e]
    exact hv'
  have hT : ∀ x ∈ (V : Set G) ∪ (Vh : Set G), q * x * q⁻¹ ∈ (V : Set G) ∪ (Vh : Set G) := by
    rintro x (hx | hx)
    · exact Or.inl (hV_conj x hx)
    · exact Or.inr (hVh_conj x hx)
  have hcl : ch82I V h = Subgroup.closure ((V : Set G) ∪ (Vh : Set G)) := by
    rw [hI, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hcl] at hi ⊢
  exact Ob5KN.conj_closure q _ hT i hi

theorem ob5_K_normalizes_P {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (c : S828Ctx T L I H h k)
    (e : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃* DihedralGroup 5)
    (hkerI : kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) =
      pCoreOf 2 (ch82I (fsuV T I) h))
    {K : Subgroup G} (hLUK : ch82LU L (ch82U (fsuV T I) h) ≤ K)
    (hKle : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))
    (hKn : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
    (hperf : ⁅K, K⁆ = K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hLUC : ¬ ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)) :
    ∃ y ∈ ch82I (fsuV T I) h, Odd (orderOf y) ∧
      ob5dd (ob5dihHom c e hkerI) y = DihedralGroup.r 1 ∧
      (∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), y * p * y⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h →
        p ∈ ch82U (fsuV T I) h) ∧
      (∀ κ ∈ K, ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
        κ * p * κ⁻¹ ∈ pCoreOf 2 (ch82I (fsuV T I) h)) ∧
      (∀ κ ∈ K, κ * y * κ⁻¹ * y⁻¹ ∈ pCoreOf 2 (ch82I (fsuV T I) h)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := ob5_setup_of_c c
  set f := ob5dihHom c e hkerI with hfdef
  have hsurj : Function.Surjective f := ob5dihHom_surj c e hkerI
  have hfP : ∀ g ∈ ch82I (fsuV T I) h, ob5dd f g = 1 ↔ g ∈ pCoreOf 2 (ch82I (fsuV T I) h) := by
    intro g hg
    have e1 : ob5dd f g = f ⟨g, hg⟩ := by
      simp only [ob5dd, dif_pos hg]
    rw [e1]
    exact ob5dihHom_ker c e hkerI ⟨g, hg⟩
  have hVI : fsuV T I ≤ ch82I (fsuV T I) h := fun x hx => Subgroup.mem_sup_left hx
  have hVhI : B6.conjSub h (fsuV T I) ≤ ch82I (fsuV T I) h := fun x hx => Subgroup.mem_sup_right hx
  have hIV : ch82I (fsuV T I) h = fsuV T I ⊔ B6.conjSub h (fsuV T I) := rfl
  obtain ⟨y, hyI, hyodd, hyr⟩ := ob5_exists_y f hsurj
  obtain ⟨v, hv, hvP⟩ := ob5_exists_v f hsurj hfP hIV c.hhI S.hPn S.hVh'
  have hw0Vh : h * v * h⁻¹ ∈ B6.conjSub h (fsuV T I) := S.hVh v hv
  have hw0I : h * v * h⁻¹ ∈ ch82I (fsuV T I) h := hVhI hw0Vh
  have hw0sq : (h * v * h⁻¹) * (h * v * h⁻¹) = 1 := S.hV2h _ hw0Vh
  have hw0P : ob5dd f (h * v * h⁻¹) ≠ 1 := by
    intro h1
    apply hvP
    rw [ob5dd_conj f c.hhI (hVI hv)] at h1
    calc ob5dd f v = (ob5dd f h)⁻¹ * (ob5dd f h * ob5dd f v * (ob5dd f h)⁻¹) * ob5dd f h := by
          group
      _ = 1 := by rw [h1]; group
  obtain ⟨j, q, hqP, hg⟩ := ob5_vw_rel f hfP hVI hyI hyr hv hvP S.hV2 hw0I hw0sq hw0P
  have hcover := ob5_V_cover f hfP S.hBdef hVI S.hV2 S.hVcomm hv hvP
  have hVhc : ∀ w ∈ B6.conjSub h (fsuV T I), ∀ w' ∈ B6.conjSub h (fsuV T I), w * w' = w' * w := by
    intro w hw w' hw'
    obtain ⟨a, ha, rfl⟩ := S.hVh' w hw
    obtain ⟨b, hb, rfl⟩ := S.hVh' w' hw'
    calc h * a * h⁻¹ * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
      _ = h * (b * a) * h⁻¹ := by rw [S.hVcomm a ha b hb]
      _ = h * b * h⁻¹ * (h * a * h⁻¹) := by group
  have hcoverh := ob5_Vh_cover f hfP S.hAdef hVhI S.hV2h hVhc hw0Vh hw0P
  have hfix : ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
      y * p * y⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h → p ∈ ch82U (fsuV T I) h :=
    fun p hp hyp => S.lemma15 y hyI v hv j q hqP hg hcover hcoverh p hp hyp
  have hXC : ¬ K ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) :=
    fun hKC => hLUC (hLUK.trans hKC)
  have hKI : ∀ κ ∈ K, ∀ i ∈ ch82I (fsuV T I) h,
      κ * i * κ⁻¹ * i⁻¹ ∈ pCoreOf 2 K := by
    intro κ hκ i hi
    have hiC : i ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 := c.hcen u hu i hi
      calc u * i = i * u * i⁻¹ * i := by rw [h1]
        _ = i * u := by group
    have hcc := commutator_centralizer_le_828 hKle hKn hperf hq hXC
    exact hcc (Subgroup.commutator_mem_commutator hκ hiC)
  have hKU : ∀ κ ∈ K, ∀ u ∈ ch82U (fsuV T I) h, κ * u * κ⁻¹ ∈ ch82U (fsuV T I) h :=
    fun κ hκ u hu => (Subgroup.mem_normalizer_iff.mp (hKle hκ) u).mp hu
  have hUP : ∀ u ∈ ch82U (fsuV T I) h, u ∈ pCoreOf 2 (ch82I (fsuV T I) h) :=
    fun u hu => ((S.hBdef u).mp (S.hUB u hu)).2
  let X : Ob5KN (ch82I (fsuV T I) h) K (ch82U (fsuV T I) h) y :=
    { hyI := hyI
      hyodd := hyodd
      hKU := hKU
      hKI := hKI
      hQI := ob5_Q_norm_I c hKle hKn hS
      hUc := fun u hu i hi => c.hcen u hu i hi
      hUP := hUP
      hPP := fun p hp q hq => c.hP2 p hp q hq
      hfix := hfix }
  have hIK : ch82I (fsuV T I) h ≤ Subgroup.normalizer (K : Set G) := by
    intro i hi
    have hiC : i ∈ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 := c.hcen u hu i hi
      calc u * i = i * u * i⁻¹ * i := by rw [h1]
        _ = i * u := by group
    exact hKn ((Subgroup.centralizer_le_normalizer _) hiC)
  have hIn : ∀ i ∈ ch82I (fsuV T I) h, ∀ q ∈ pCoreOf 2 K, i * q * i⁻¹ ∈ pCoreOf 2 K :=
    fun i hi q hq =>
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hIK hi)) q).mp hq
  have hcommy : ∀ κ ∈ K, κ * y * κ⁻¹ * y⁻¹ ∈ pCoreOf 2 (ch82I (fsuV T I) h) := by
    intro κ hκ
    have hc' : κ * y * κ⁻¹ * y⁻¹ ∈ pCoreOf 2 K := hKI κ hκ y hyI
    have hconj : κ * y * κ⁻¹ ∈ ch82I (fsuV T I) h := by
      have e : κ * y * κ⁻¹ = (κ * y * κ⁻¹ * y⁻¹) * y := by group
      have hJ : κ * y * κ⁻¹ ∈ ch82I (fsuV T I) h ⊔ pCoreOf 2 K := by
        rw [e]
        exact (ch82I (fsuV T I) h ⊔ pCoreOf 2 K).mul_mem
          ((le_sup_right : pCoreOf 2 K ≤ ch82I (fsuV T I) h ⊔ pCoreOf 2 K) hc')
          ((le_sup_left : ch82I (fsuV T I) h ≤ ch82I (fsuV T I) h ⊔ pCoreOf 2 K) hyI)
      exact X.odd_mem_I _ hJ (by rw [Ob5KN.orderOf_conj']; exact hyodd)
    have hc'' : κ * y * κ⁻¹ * y⁻¹ ∈ ch82I (fsuV T I) h :=
      (ch82I (fsuV T I) h).mul_mem hconj ((ch82I (fsuV T I) h).inv_mem hyI)
    exact (ob5_O2K_inter_le hIn) (Subgroup.mem_inf.mpr ⟨hc', hc''⟩)
  exact ⟨y, hyI, hyodd, hyr, hfix, fun κ hκ p hp => Ob5KN.K_norm X κ hκ p hp, hcommy⟩

end Glue3

end CFSG.Quasithin.H13
