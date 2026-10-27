module

public import CFSG.Quasithin.EmptyFaithful.S14114
public import CFSG.Quasithin.EmptyFaithful.S14118
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp14117 (T Mc M M₁ V : Subgroup G) : Prop where
  inM : InM T M
  twoReduced : IsTwoReducedIn M V
  ne_bot : V ≠ ⊥
  inM₁ : InM T M₁
  ne : M₁ ≠ M
  cases : (OrdLE T M₁ M ∧ V = VZ T M) ∨ M₁ = Mc

theorem exists_ne_one_mem_omegaOneCenter_of_normalized {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hU : U ≠ ⊥) (hn : T ≤ Subgroup.normalizer (U : Set G)) :
    ∃ z ∈ U, z ≠ 1 ∧ z ∈ quasithinOmegaOneCenter T := by
  have hTnil : Group.IsNilpotent T := hT.isNilpotent
  have hUTn : (U.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mpr hn
  have hU' : U.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, hbot, Subgroup.map_bot]
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hU')
  have hwU : (w : G) ∈ U := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1
  have hwc : ∀ y ∈ T, (y : G) * w = w * y := fun y hy => by
    have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hw1' : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨k, hk⟩ := hT w
  have hk' : (w : G) ^ 2 ^ k = 1 := by simpa using congrArg (fun u : T => (u : G)) hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_dvd_of_pow_eq_one hk' : orderOf (w : G) ∣ 2 ^ k)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hw1' (orderOf_eq_one_iff.mp (by simpa using hj))
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  set z : G := (w : G) ^ 2 ^ i with hz
  have hzU : z ∈ U := Subgroup.pow_mem U hwU _
  have hzT : z ∈ T := Subgroup.pow_mem T w.2 _
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, ← pow_succ, ← hj]
    exact pow_orderOf_eq_one _
  have hz1 : z ≠ 1 := by
    intro h1
    have : orderOf (w : G) ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at this
    have := Nat.le_of_dvd (by positivity) this
    have h2 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨z, hzU, hz1, Subgroup.subset_closure ⟨⟨hzT, ?_⟩, hz2⟩⟩
  show z ∈ Subgroup.centralizer (T : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Commute.pow_right (show Commute y (w : G) from hwc y hy) _).eq

theorem centralizer_singleton_le_mc_of_mem_omegaOneCenter {T Mc : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Mc := by
  have hzT : z ∈ T := (quasithinOmegaOneCenter_le_center T hz).1
  set P : Subgroup G := Subgroup.zpowers z with hP
  have hPp : IsPGroup 2 P := h.sylow.1.to_le (Subgroup.zpowers_le.mpr hzT)
  have hP1 : P ≠ ⊥ := fun hb => hz1 ((Subgroup.zpowers_eq_bot).mp hb)
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    have : Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer (P : Set G) := by
      rw [hP, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [this]
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨M'', hM'', hNM''⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (P : Set G)) ⟨P, hP1, hPp, rfl⟩
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M'' :=
    le_trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz)) (hCN.trans hNM'')
  rw [← h.mc_unique M'' hM'' hCZ]
  exact hCN.trans hNM''

omit [Finite G] in
theorem mem_autOn_iff_exists {X V : Subgroup G} {a : MulAut V} :
    a ∈ autOn X V ↔ ∃ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ X ∧
      conjAct V ⟨x, hx⟩ = a :=
  CFSG.Quasithin.AutOn.mem_autOn_iff_exists

omit [Finite G] in
theorem conjAct_conj {V : Subgroup G} {g r : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hr : r ∈ Subgroup.normalizer (V : Set G)) (hgr : g * r * g⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨g * r * g⁻¹, hgr⟩ = conjAct V ⟨g, hg⟩ * conjAct V ⟨r, hr⟩ * (conjAct V ⟨g, hg⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite G] in
theorem conjAct_inv {V : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hg' : g⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨g⁻¹, hg'⟩ = (conjAct V ⟨g, hg⟩)⁻¹ := by
  rw [← map_inv]
  rfl

namespace Hyp14117

variable {T Mc M M₁ V : Subgroup G}

omit [Finite G] in
theorem le_inf (hyp : Hyp14117 T Mc M M₁ V) : T ≤ M₁ ⊓ M := _root_.le_inf hyp.inM₁.2 hyp.inM.2

omit [Finite G] in
theorem le_normalizer (hyp : Hyp14117 T Mc M M₁ V) : M ≤ Subgroup.normalizer (V : Set G) :=
  hyp.twoReduced.2.1

theorem V_le (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) : V ≤ T := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have := le_sylow_of_isTwoReducedIn S (hS ▸ hyp.inM.2) hyp.twoReduced
  rwa [hS] at this

theorem centralizer_le (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) :
    M ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ M₁ := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  rcases hyp.cases with ⟨hle, hV⟩ | hM₁
  · have hHv : IsHv T M₁ := by
      have := isHv_of_inM h.qtke.2.1 S (hS ▸ hyp.inM₁)
      rwa [hS] at this
    have h1 := centralizer_VZ_le_of_ordLE_of_isHv hle hHv
    rw [hV]
    exact fun x hx => ⟨hx.1, (h1 hx).1⟩
  · obtain ⟨z, hzV, hz1, hzZ⟩ := exists_ne_one_mem_omegaOneCenter_of_normalized h.sylow.1
      (hyp.V_le h) hyp.ne_bot (hyp.inM.2.trans hyp.le_normalizer)
    have hC : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzV)
    exact fun x hx => ⟨hx.1, hM₁ ▸ centralizer_singleton_le_mc_of_mem_omegaOneCenter h hzZ hz1
      (hC hx.2)⟩

theorem centralizer_le_normalizer (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) :
    M ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (pCoreOf 2 (M₁ ⊓ M) : Set G) := by
  intro x hx
  have h1 : x ∈ M₁ ⊓ M := by
    have := hyp.centralizer_le h hx
    rwa [inf_comm] at this
  exact le_normalizer_pCoreOf 2 (M₁ ⊓ M) h1

theorem pCoreOf_le_sylow (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) :
    pCoreOf 2 (M₁ ⊓ M) ≤ T := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have := pCoreOf_two_le_sylow (M₁ ⊓ M) S (hS ▸ hyp.le_inf)
  rwa [hS] at this

theorem pCoreOf_le_pCoreOf_inf (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) :
    pCoreOf 2 M ≤ pCoreOf 2 (M₁ ⊓ M) := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have := pCoreOf_le_pCoreOf_inf_of_sylow (T := S) (hS ▸ hyp.inM.2) (hS ▸ hyp.inM₁.2)
  rwa [inf_comm] at this

theorem pCoreOf_le_centralizer (hyp : Hyp14117 T Mc M M₁ V) :
    pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G) := by
  refine hyp.twoReduced.2.2.2 (pCoreOf 2 M) (pCoreOf_le 2 M) (le_normalizer_pCoreOf 2 M) ?_
  intro d hd
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem le_normalizer_inf_centralizer (hyp : Hyp14117 T Mc M M₁ V) :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, normalizer_le_normalizer_centralizer V (hyp.le_normalizer hg)⟩

theorem inf_centralizer_eq (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) :
    pCoreOf 2 (M₁ ⊓ M) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 M := by
  have hRM : pCoreOf 2 (M₁ ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  refine le_antisymm ?_ (_root_.le_inf (hyp.pCoreOf_le_pCoreOf_inf h) hyp.pCoreOf_le_centralizer)
  set C : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCn : C ≤ Subgroup.normalizer
      ((pCoreOf 2 (M₁ ⊓ M) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro c hc
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hyp.centralizer_le_normalizer h hc, normalizer_le_normalizer_centralizer V
        (hyp.le_normalizer hc.1)⟩
  have h1 : pCoreOf 2 (M₁ ⊓ M) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 C :=
    le_pCoreOf_of_le_normalizer 2 (fun x hx => ⟨hRM hx.1, hx.2⟩) hCn
      ((pCoreOf_isPGroup 2 (M₁ ⊓ M)).to_le inf_le_left)
  refine h1.trans (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans inf_le_left) ?_
    (pCoreOf_isPGroup 2 C))
  exact (hyp.le_normalizer_inf_centralizer).trans (normalizer_le_normalizer_pCoreOf 2 C)

theorem pCoreOf_eq_pCoreOf_sup (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) :
    pCoreOf 2 (M₁ ⊓ M) =
      pCoreOf 2 ((M ⊓ Subgroup.centralizer (V : Set G)) ⊔ pCoreOf 2 (M₁ ⊓ M)) := by
  set R : Subgroup G := pCoreOf 2 (M₁ ⊓ M) with hR
  set C : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hC
  have hRp : IsPGroup 2 R := pCoreOf_isPGroup 2 _
  have hCn : C ≤ Subgroup.normalizer (R : Set G) := hyp.centralizer_le_normalizer h
  have hJn : C ⊔ R ≤ Subgroup.normalizer (R : Set G) := sup_le hCn Subgroup.le_normalizer
  have hRJ : R ≤ pCoreOf 2 (C ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 le_sup_right hJn hRp
  refine le_antisymm hRJ ?_
  set Q : Subgroup G := pCoreOf 2 (C ⊔ R) with hQ
  intro q hq
  have hqJ : q ∈ R ⊔ C := by
    rw [sup_comm]
    exact pCoreOf_le 2 _ hq
  have hmul : ((R ⊔ C : Subgroup G) : Set G) = (R : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R C hCn
  have hqJ' : q ∈ (R : Set G) * (C : Set G) := by rw [← hmul]; exact hqJ
  obtain ⟨r, hr, c, hc, rfl⟩ := hqJ'
  have hcQ : c ∈ Q := by
    have h1 : r⁻¹ * (r * c) ∈ Q := Q.mul_mem (Q.inv_mem (hRJ hr)) hq
    simpa using h1
  have hQn : C ≤ Subgroup.normalizer (Q : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 (C ⊔ R))
  have hcQC : c ∈ pCoreOf 2 C := by
    refine le_pCoreOf_of_le_normalizer 2 (N := Q ⊓ C) inf_le_right ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left) ⟨hcQ, hc⟩
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hQn hx, Subgroup.le_normalizer hx⟩
  have hcO : c ∈ pCoreOf 2 M := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans inf_le_left) ?_
      (pCoreOf_isPGroup 2 C) hcQC
    exact (hyp.le_normalizer_inf_centralizer).trans (normalizer_le_normalizer_pCoreOf 2 C)
  exact R.mul_mem hr (hyp.pCoreOf_le_pCoreOf_inf h hcO)

theorem autOn_inf_normalizer_eq (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) :
    autOn M V ⊓ Subgroup.normalizer (autOn (pCoreOf 2 (M₁ ⊓ M)) V : Set (MulAut V)) =
      autOn (M ⊓ Subgroup.normalizer (pCoreOf 2 (M₁ ⊓ M) : Set G)) V := by
  set R : Subgroup G := pCoreOf 2 (M₁ ⊓ M) with hR
  set C : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hC
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hyp.le_normalizer
  have hRM : R ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hCn : C ≤ Subgroup.normalizer (R : Set G) := hyp.centralizer_le_normalizer h
  have hJ : R = pCoreOf 2 (C ⊔ R) := hyp.pCoreOf_eq_pCoreOf_sup h
  have hmul : ((R ⊔ C : Subgroup G) : Set G) = (R : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R C hCn
  have K1 : ∀ (g : G) (hg : g ∈ M), conjAct V ⟨g, hMV hg⟩ ∈
      Subgroup.normalizer (autOn R V : Set (MulAut V)) → ∀ r ∈ R, g * r * g⁻¹ ∈ C ⊔ R := by
    intro g hg hn r hr
    have hrV : r ∈ Subgroup.normalizer (V : Set G) := hMV (hRM hr)
    have hgrM : g * r * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg (hRM hr)) (M.inv_mem hg)
    have hgrV : g * r * g⁻¹ ∈ Subgroup.normalizer (V : Set G) := hMV hgrM
    have hr' : conjAct V ⟨r, hrV⟩ ∈ autOn R V := mem_autOn_iff_exists.mpr ⟨r, hrV, hr, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hn _).mp hr'
    rw [← conjAct_conj (hMV hg) hrV hgrV] at h1
    obtain ⟨r', hr'V, hr'R, hr'eq⟩ := mem_autOn_iff_exists.mp h1
    have hc : r'⁻¹ * (g * r * g⁻¹) ∈ Subgroup.centralizer (V : Set G) := by
      have hinv : r'⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hr'V
      have hprodV : r'⁻¹ * (g * r * g⁻¹) ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.mul_mem _ hinv hgrV
      have h2 : conjAct V ⟨r'⁻¹ * (g * r * g⁻¹), hprodV⟩ = 1 := by
        have e1 : conjAct V ⟨r'⁻¹ * (g * r * g⁻¹), hprodV⟩ =
            (conjAct V ⟨r', hr'V⟩)⁻¹ * conjAct V ⟨g * r * g⁻¹, hgrV⟩ := by
          rw [← map_inv, ← map_mul]
          rfl
        rw [e1, hr'eq]
        exact inv_mul_cancel _
      exact A4.conjAct_eq_one_iff.mp h2
    have hcM : r'⁻¹ * (g * r * g⁻¹) ∈ M := M.mul_mem (M.inv_mem (hRM hr'R)) hgrM
    have e : g * r * g⁻¹ = r' * (r'⁻¹ * (g * r * g⁻¹)) := by group
    rw [e]
    exact (C ⊔ R).mul_mem (Subgroup.mem_sup_right hr'R) (Subgroup.mem_sup_left ⟨hcM, hc⟩)
  ext a
  constructor
  · rintro ⟨haM, haN⟩
    obtain ⟨g, hgV, hgM, rfl⟩ := mem_autOn_iff_exists.mp haM
    have hgN : g ∈ Subgroup.normalizer ((C ⊔ R : Subgroup G) : Set G) := by
      have fwd : ∀ (g' : G) (hg' : g' ∈ M), conjAct V ⟨g', hMV hg'⟩ ∈
          Subgroup.normalizer (autOn R V : Set (MulAut V)) →
            ∀ x ∈ C ⊔ R, g' * x * g'⁻¹ ∈ C ⊔ R := by
        intro g' hg' hn x hx
        have hx' : x ∈ (R : Set G) * (C : Set G) := by
          rw [← hmul]
          rwa [sup_comm] at hx
        obtain ⟨r, hr, c, hc, rfl⟩ := hx'
        have e : g' * (r * c) * g'⁻¹ = (g' * r * g'⁻¹) * (g' * c * g'⁻¹) := by group
        rw [e]
        refine (C ⊔ R).mul_mem (K1 g' hg' hn r hr) (Subgroup.mem_sup_left ?_)
        exact (Subgroup.mem_normalizer_iff.mp (hyp.le_normalizer_inf_centralizer hg') c).mp hc
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fwd g hgM haN x, fun hx => ?_⟩
      have hinv : conjAct V ⟨g⁻¹, hMV (M.inv_mem hgM)⟩ ∈
          Subgroup.normalizer (autOn R V : Set (MulAut V)) := by
        rw [conjAct_inv hgV (hMV (M.inv_mem hgM))]
        exact Subgroup.inv_mem _ haN
      have := fwd g⁻¹ (M.inv_mem hgM) hinv _ hx
      simpa [mul_assoc] using this
    have hgNR : g ∈ Subgroup.normalizer (R : Set G) := by
      have := normalizer_le_normalizer_pCoreOf 2 (C ⊔ R) hgN
      rwa [← hJ] at this
    exact mem_autOn_iff_exists.mpr ⟨g, hgV, ⟨hgM, hgNR⟩, rfl⟩
  · intro ha
    obtain ⟨g, hgV, ⟨hgM, hgN⟩, rfl⟩ := mem_autOn_iff_exists.mp ha
    have fwd : ∀ (g' : G) (hg' : g' ∈ M ⊓ Subgroup.normalizer (R : Set G))
        (hg'V : g' ∈ Subgroup.normalizer (V : Set G)) (b : MulAut V), b ∈ autOn R V →
          conjAct V ⟨g', hg'V⟩ * b * (conjAct V ⟨g', hg'V⟩)⁻¹ ∈ autOn R V := by
      intro g' hg' hg'V b hb
      obtain ⟨r, hrV, hr, rfl⟩ := mem_autOn_iff_exists.mp hb
      have hgr : g' * r * g'⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg'.2 r).mp hr
      have hgrV : g' * r * g'⁻¹ ∈ Subgroup.normalizer (V : Set G) := hMV (hRM hgr)
      rw [← conjAct_conj hg'V hrV hgrV]
      exact mem_autOn_iff_exists.mpr ⟨_, hgrV, hgr, rfl⟩
    refine ⟨A4.autOn_mono inf_le_left ha, Subgroup.mem_normalizer_iff.mpr fun b => ?_⟩
    refine ⟨fwd g ⟨hgM, hgN⟩ hgV b, fun hb => ?_⟩
    have hinvmem : g⁻¹ ∈ M ⊓ Subgroup.normalizer (R : Set G) :=
      (M ⊓ Subgroup.normalizer (R : Set G)).inv_mem ⟨hgM, hgN⟩
    have hgV' : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hgV
    have := fwd g⁻¹ hinvmem hgV' _ hb
    rw [conjAct_inv hgV hgV'] at this
    have e : (conjAct V ⟨g, hgV⟩)⁻¹ * (conjAct V ⟨g, hgV⟩ * b * (conjAct V ⟨g, hgV⟩)⁻¹) *
        ((conjAct V ⟨g, hgV⟩)⁻¹)⁻¹ = b := by group
    rwa [e] at this

end Hyp14117

theorem lemma_14_1_17_one {T Mc M M₁ V : Subgroup G} (h113 : StageLemma14113)
    (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) :
    autOn (pCoreOf 2 (M₁ ⊓ M)) V ≠ ⊥ := by
  intro hbot
  have hRM : pCoreOf 2 (M₁ ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hRV : pCoreOf 2 (M₁ ⊓ M) ≤ Subgroup.normalizer (V : Set G) := hRM.trans hyp.le_normalizer
  have hRC : pCoreOf 2 (M₁ ⊓ M) ≤ Subgroup.centralizer (V : Set G) := by
    intro r hr
    have hmem : conjAct V ⟨r, hRV hr⟩ ∈ autOn (pCoreOf 2 (M₁ ⊓ M)) V :=
      mem_autOn_iff_exists.mpr ⟨r, hRV hr, hr, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact A4.conjAct_eq_one_iff.mp hmem
  have h1 : pCoreOf 2 (M₁ ⊓ M) ≤ pCoreOf 2 M := by
    rw [← hyp.inf_centralizer_eq h]
    exact le_inf le_rfl hRC
  exact not_lt_of_ge h1 (lemma_14_1_14 h113 h hyp.inM hyp.inM₁ hyp.ne).1

theorem lemma_14_1_17_five {T Mc M M₁ V : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hyp : Hyp14117 T Mc M M₁ V) :
    pCoreOf 2 (M₁ ⊓ M) =
        pCoreOf 2 ((M ⊓ Subgroup.centralizer (V : Set G)) ⊔ pCoreOf 2 (M₁ ⊓ M)) ∧
      autOn M V ⊓ Subgroup.normalizer (autOn (pCoreOf 2 (M₁ ⊓ M)) V : Set (MulAut V)) =
        autOn (M ⊓ Subgroup.normalizer (pCoreOf 2 (M₁ ⊓ M) : Set G)) V :=
  ⟨hyp.pCoreOf_eq_pCoreOf_sup h, hyp.autOn_inf_normalizer_eq h⟩

end CFSG.Quasithin
