module

public import CFSG.Quasithin.H13.A6S13822b
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace A6Gen

variable {G : Type} [Group G] [Finite G]

theorem mIdx_le_of_le {X Y Z : Subgroup G} (hX : IsPGroup 2 X) (hYZ : Y ≤ Z) :
    mIdx X Z ≤ mIdx X Y := by
  have h1 := Subgroup.relIndex_dvd_of_le_left (L := X) hYZ
  rw [HypF98.relIndex_eq_two_pow_mIdx hX, HypF98.relIndex_eq_two_pow_mIdx hX] at h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1

theorem eq_of_mIdx_eq {X Y Z : Subgroup G} (hX : IsPGroup 2 X) (hYZ : Y ≤ Z) (hZX : Z ≤ X)
    (h : mIdx X Z = mIdx X Y) : Y = Z := by
  have h1 := Subgroup.relIndex_mul_relIndex Y Z X hYZ hZX
  rw [HypF98.relIndex_eq_two_pow_mIdx hX, HypF98.relIndex_eq_two_pow_mIdx hX, h] at h1
  have h2 : Y.relIndex Z = 1 := by
    have hpos : 0 < 2 ^ mIdx X Y := by positivity
    nlinarith
  exact le_antisymm hYZ (Subgroup.relIndex_eq_one.1 h2)

omit [Finite G] in
theorem pow_mul_inv_mem {K : Subgroup G} {t k : G} (ht : t ∈ Subgroup.normalizer (K : Set G))
    (hk : k ∈ K) (n : ℕ) : (t * k) ^ n * (t ^ n)⁻¹ ∈ K := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htn : t ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ ht n
    have h1 : t ^ (n + 1) * k * (t ^ (n + 1))⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht (n + 1)) k).mp hk
    have e : (t * k) ^ (n + 1) * (t ^ (n + 1))⁻¹ =
        ((t * k) ^ n * (t ^ n)⁻¹) * (t ^ (n + 1) * k * (t ^ (n + 1))⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact K.mul_mem ih h1

omit [Finite G] in
theorem conj_eq_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) {g a : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) (ha : a ∈ A) : g * a * g⁻¹ = a := by
  by_cases ha1 : a = 1
  · rw [ha1]; group
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA
  have hga : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have h1 : (⟨a, ha⟩ : ↥A) = y := huniq _ (fun h => ha1 (congrArg Subtype.val h))
  have h2 : (⟨g * a * g⁻¹, hga⟩ : ↥A) = y := huniq _ (fun h => ha1 (by
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    rw [mul_inv_eq_one, mul_eq_left] at this
    exact this))
  exact congrArg Subtype.val (h2.trans h1.symm)

end A6Gen

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_pCoreOf_of_trivial (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ T)
    (hsimp : IsSimpleGroup ↥(S.KSt H K)) {X Y : Subgroup G} (hXU : X ≤ conjClosure S.V3 H)
    (hV1Y : fsuV1 T V ≤ Y) (hHX : H ≤ Subgroup.normalizer (X : Set G))
    (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (hKnt : ∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ Y) {h : G} (hh : h ∈ H)
    (htriv : ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ Y) : h ∈ pCoreOf 2 H := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF1 := (hS.hF H hH).toHypF91
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF1.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF1.isElemAbelian_tilde⟩
  set φ := actH hV₁ hIH with hφ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hXH : X ≤ H := hXU.trans (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H))
  let C : Subgroup G :=
    { carrier := {c | c ∈ H ∧ ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ Y}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H.mul_mem ha hb, fun x hx => ?_⟩
        have h1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hHY ha) _).mp (hb' x hx)
        have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
            (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact Y.mul_mem h1 (ha' x hx)
      one_mem' := ⟨H.one_mem, fun x _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H.inv_mem ha, fun x hx => ?_⟩
        have hxi : x⁻¹ ∈ X := X.inv_mem hx
        have h1 := ha' _ hxi
        have hax : a⁻¹ * x ∈ H := H.mul_mem (H.inv_mem ha) (hXH hx)
        have h2 := (Subgroup.mem_normalizer_iff.mp (hHY hax) _).mp h1
        have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ =
            (a⁻¹ * x) * (a * x⁻¹ * a⁻¹ * x⁻¹⁻¹) * (a⁻¹ * x)⁻¹ := by group
        rw [e]
        exact h2 }
  have hmemC : ∀ c, c ∈ C ↔ c ∈ H ∧ ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ Y := fun c => Iff.rfl
  have hQC : pCoreOf 2 H ≤ C := by
    intro q hq
    have hq' := hq
    rw [hF1.pCoreOf_eq_centralizerMod] at hq'
    exact ⟨hq'.1, fun x hx => hV1Y (hq'.2.2 x (hXU hx))⟩
  have hconjC : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    rintro g hg c ⟨hc, hc'⟩
    refine ⟨H.mul_mem (H.mul_mem hg hc) (H.inv_mem hg), fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hHX (H.inv_mem hg)) x).mp hx
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHY hg) _).mp (hc' _ hx')
    have e : g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹ * x⁻¹ =
        g * (c * (g⁻¹ * x * g) * c⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1
  have hCn : H ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hconjC g hg c hc, fun hc => ?_⟩
    have := hconjC g⁻¹ (H.inv_mem hg) _ hc
    simpa [mul_assoc] using this
  have hKst : S.KSt H K = (K.subgroupOf H).map φ := autOn_tilde_eq_map_actH hV₁ hIH hKH
  have hKC : K ⊓ C ≤ pCoreOf 2 H := by
    set M := ((K ⊓ C).subgroupOf H).map φ with hM
    have hMn : (M.subgroupOf (S.KSt H K)).Normal := by
      refine ⟨fun m hm a => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      obtain ⟨y, hy, hym⟩ := hm
      obtain ⟨k, hk, hka⟩ := hKst.le a.2
      have hyK := (Subgroup.mem_subgroupOf.1 hy).1
      have hyC := (Subgroup.mem_subgroupOf.1 hy).2
      have hkK := Subgroup.mem_subgroupOf.1 hk
      refine ⟨k * y * k⁻¹, Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩, ?_⟩
      · exact K.mul_mem (K.mul_mem hkK hyK) (K.inv_mem hkK)
      · exact hconjC _ (hKH hkK) _ hyC
      · rw [map_mul, map_mul, map_inv, hka, hym]
        simp
    have := hsimp
    rcases hMn.eq_bot_or_eq_top with hb | ht
    · intro y hy
      have hyH : y ∈ H := hKH hy.1
      have hφy : φ ⟨y, hyH⟩ ∈ S.KSt H K := by
        rw [hKst]
        exact ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.2 hy.1, rfl⟩
      have hmem : (⟨φ ⟨y, hyH⟩, hφy⟩ : ↥(S.KSt H K)) ∈ M.subgroupOf (S.KSt H K) :=
        Subgroup.mem_subgroupOf.2 ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmem
      exact (hker _).1 (congrArg Subtype.val hmem)
    · exfalso
      obtain ⟨k, hk, x, hx, hkx⟩ := hKnt
      apply hkx
      have hkH : k ∈ H := hKH hk
      have hφk : φ ⟨k, hkH⟩ ∈ S.KSt H K := by
        rw [hKst]
        exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
      have hmem : (⟨φ ⟨k, hkH⟩, hφk⟩ : ↥(S.KSt H K)) ∈ M.subgroupOf (S.KSt H K) := by
        rw [ht]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyk⟩ := Subgroup.mem_subgroupOf.1 hmem
      have hq : ((y⁻¹ * ⟨k, hkH⟩ : ↥H) : G) ∈ pCoreOf 2 H :=
        (hker _).1 (by rw [map_mul, map_inv, hyk, inv_mul_cancel])
      have hkC : k ∈ C := by
        have h1 := C.mul_mem (Subgroup.mem_subgroupOf.1 hy).2 (hQC hq)
        simpa using h1
      exact hkC.2 x hx
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hTn : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hKn
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right T K hTn
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hCp : IsPGroup 2 C := by
    intro c
    have hc' : (c : G) ∈ ((T ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm, ← hHK]
      exact c.2.1
    rw [hset] at hc'
    obtain ⟨t, ht, k, hk, htk⟩ := hc'
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have h1 := A6Gen.pow_mul_inv_mem (hTn ht) hk (2 ^ a)
    have htk' : t * k = (c : G) := htk
    rw [hta, inv_one, mul_one, htk'] at h1
    have h3 : (c : G) ^ 2 ^ a ∈ pCoreOf 2 H := hKC ⟨h1, C.pow_mem c.2 _⟩
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 H ⟨_, h3⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((c : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb']
  have hCH : C ≤ H := fun c hc => hc.1
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCH hCn hCp ⟨hh, htriv⟩

theorem comm_mem_A₁_of_cent (hS : S.Hyp138)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) {c : G}
    (hcU : c ∈ conjClosure S.V3 H) (hcC : ∀ x ∈ F8.Uγ S.V3 H (g : G), x * c = c * x) {v : G}
    (hv : v ∈ F8.Uγ V H (g : G)) : v * c * v⁻¹ * c⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) := by
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hUst : conjClosure S.V3 H ≤ stab γ :=
    (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans
      inf_le_right))
  have hxG : (g : G)⁻¹ * c * (g : G) ∈ H := by
    have := hUst hcU
    rw [hstab, mem_conjSub] at this
    exact this
  have hxC : (g : G)⁻¹ * c * (g : G) ∈ Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u' hu'
    have e := hcC _ (mul_mem_conjSub (g := (g : G)) hu')
    calc u' * ((g : G)⁻¹ * c * (g : G)) =
        (g : G)⁻¹ * (((g : G) * u' * (g : G)⁻¹) * c) * (g : G) := by group
      _ = (g : G)⁻¹ * (c * ((g : G) * u' * (g : G)⁻¹)) * (g : G) := by rw [e]
      _ = ((g : G)⁻¹ * c * (g : G)) * u' := by group
  have hxQ : (g : G)⁻¹ * c * (g : G) ∈ pCoreOf 2 H := by
    rw [hF1.pCoreOf_eq_centralizerMod]
    refine ⟨hxG, hF1.H_normalizes_V₁ hxG, fun u' hu' => ?_⟩
    rw [← Subgroup.mem_centralizer_iff.mp hxC u' hu', mul_inv_cancel_right, mul_inv_cancel]
    exact (fsuV1 T V).one_mem
  have hy : (g : G)⁻¹ * v * (g : G) ∈ conjClosure V H := mem_conjSub.mp hv
  have h3 := S.comm_VH_HC hS.hNS h13315 h1356two hH hxQ hxC hy
  rw [F8.A₁, mem_conjSub]
  have e : (g : G)⁻¹ * (v * c * v⁻¹ * c⁻¹) * (g : G) =
      ((g : G)⁻¹ * v * (g : G)) * ((g : G)⁻¹ * c * (g : G)) * ((g : G)⁻¹ * v * (g : G))⁻¹ *
        ((g : G)⁻¹ * c * (g : G))⁻¹ := by group
  rw [e]
  exact h3

theorem relIndex_CH_le (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hm1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1)
    {x : G} (hxU : x ∈ F8.Uγ S.V3 H (g : G)) (hxD : x ∉ F8.Dγ S.V3 (fsuV1 T V) H (g : G)) :
    (conjClosure S.V3 H ⊓ Subgroup.centralizer (F8.Uγ S.V3 H (g : G) : Set G)).relIndex
      (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤ 2 := by
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  set DH := F8.DH S.V3 (fsuV1 T V) H (g : G) with hDHdef
  set A₁ := F8.A₁ (fsuV1 T V) (g : G) with hA₁def
  have hcA : Nat.card ↥A₁ = 2 := by
    rw [← hF1.card_V₁]
    exact Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective
  have hA₁N : A₁ ≤ Subgroup.normalizer (A₁ : Set G) := Subgroup.le_normalizer
  have hU2 : IsPGroup 2 (F8.Uγ S.V3 H (g : G)) := isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have hidx : ((F8.Dγ S.V3 (fsuV1 T V) H (g : G)).subgroupOf (F8.Uγ S.V3 H (g : G))).index = 2 := by
    have := HypF98.relIndex_eq_two_pow_mIdx (Y := F8.Dγ S.V3 (fsuV1 T V) H (g : G)) hU2
    rw [hm1, pow_one] at this
    exact this
  have hDx : ∀ d ∈ DH, d * x * d⁻¹ * x⁻¹ ∈ A₁ := fun d hd => hd.2.2 x hxU
  let δ : ↥DH →* ↥A₁ :=
    { toFun := fun d => ⟨(d : G) * x * (d : G)⁻¹ * x⁻¹, hDx d d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a * b : ↥DH) : G) * x * ((a * b : ↥DH) : G)⁻¹ * x⁻¹ =
          ((a : G) * x * (a : G)⁻¹ * x⁻¹) * ((b : G) * x * (b : G)⁻¹ * x⁻¹)
        have h1 := A6Gen.conj_eq_of_card_two hcA a.2.2.1 (hDx b b.2)
        have h2 := A6Gen.conj_eq_of_card_two hcA (hA₁N (hDx a a.2)) (hDx b b.2)
        have e : ((a * b : ↥DH) : G) * x * ((a * b : ↥DH) : G)⁻¹ * x⁻¹ =
            ((a : G) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) * (a : G)⁻¹) *
              ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [e, h1]
        calc ((b : G) * x * (b : G)⁻¹ * x⁻¹) * ((a : G) * x * (a : G)⁻¹ * x⁻¹) =
            (((a : G) * x * (a : G)⁻¹ * x⁻¹) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) *
              ((a : G) * x * (a : G)⁻¹ * x⁻¹)⁻¹) * ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by
              rw [h2]
          _ = _ := by group }
  have hker : δ.ker ≤
      (conjClosure S.V3 H ⊓ Subgroup.centralizer (F8.Uγ S.V3 H (g : G) : Set G)).subgroupOf DH := by
    intro d hd
    have hd1 : (d : G) * x * (d : G)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
    have hdx : x * (d : G) = (d : G) * x := by
      calc x * (d : G) = ((d : G) * x * (d : G)⁻¹ * x⁻¹)⁻¹ * ((d : G) * x) := by group
        _ = (d : G) * x := by rw [hd1, inv_one, one_mul]
    rw [Subgroup.mem_subgroupOf]
    refine ⟨d.2.1, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    by_cases huD : u ∈ F8.Dγ S.V3 (fsuV1 T V) H (g : G)
    · have h1 := Subgroup.commutator_mem_commutator d.2 huD
      rw [hF.F913_7 s, Subgroup.mem_bot, commutatorElement_def] at h1
      calc u * (d : G) = ((d : G) * u * (d : G)⁻¹ * u⁻¹)⁻¹ * ((d : G) * u) := by group
        _ = (d : G) * u := by rw [h1, inv_one, one_mul]
    · have hxu : x⁻¹ * u ∈ F8.Dγ S.V3 (fsuV1 T V) H (g : G) := by
        have hiff : ((⟨x, hxU⟩ : ↥(F8.Uγ S.V3 H (g : G)))⁻¹ ∈
              (F8.Dγ S.V3 (fsuV1 T V) H (g : G)).subgroupOf (F8.Uγ S.V3 H (g : G)) ↔
            (⟨u, hu⟩ : ↥(F8.Uγ S.V3 H (g : G))) ∈
              (F8.Dγ S.V3 (fsuV1 T V) H (g : G)).subgroupOf (F8.Uγ S.V3 H (g : G))) := by
          constructor
          · intro h
            exfalso
            apply hxD
            have h' := (F8.Dγ S.V3 (fsuV1 T V) H (g : G)).inv_mem (Subgroup.mem_subgroupOf.1 h)
            simpa using h'
          · intro h
            exact absurd (Subgroup.mem_subgroupOf.1 h) huD
        have h1 := (Subgroup.mul_mem_iff_of_index_two hidx).2 hiff
        simpa using Subgroup.mem_subgroupOf.1 h1
      have h1 := Subgroup.commutator_mem_commutator d.2 hxu
      rw [hF.F913_7 s, Subgroup.mem_bot, commutatorElement_def] at h1
      have hc : (x⁻¹ * u) * (d : G) = (d : G) * (x⁻¹ * u) := by
        calc (x⁻¹ * u) * (d : G) = ((d : G) * (x⁻¹ * u) * (d : G)⁻¹ * (x⁻¹ * u)⁻¹)⁻¹ *
            ((d : G) * (x⁻¹ * u)) := by group
          _ = (d : G) * (x⁻¹ * u) := by rw [h1, inv_one, one_mul]
      calc u * (d : G) = x * ((x⁻¹ * u) * (d : G)) := by group
        _ = x * ((d : G) * (x⁻¹ * u)) := by rw [hc]
        _ = (x * (d : G)) * (x⁻¹ * u) := by group
        _ = ((d : G) * x) * (x⁻¹ * u) := by rw [hdx]
        _ = (d : G) * u := by group
  have h1 := Subgroup.index_dvd_of_le hker
  have h2 := Subgroup.index_ker δ
  have h3 : Nat.card ↥δ.range ≤ 2 := hcA ▸ Subgroup.card_le_card_group δ.range
  have h4 : δ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h5 := Nat.le_of_dvd (Nat.pos_of_ne_zero h4) h1
  show ((conjClosure S.V3 H ⊓
    Subgroup.centralizer (F8.Uγ S.V3 H (g : G) : Set G)).subgroupOf DH).index ≤ 2
  omega

end Setting4

theorem isSimpleGroup_of_list1821 {X : Type} [Group X]
    (h : IsPSL 3 2 1 X ∨ IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X ∨ IsAlt 6 X ∨ IsAlt 7 X ∨
      IsPSU 3 3 1 X) : IsSimpleGroup X := by
  rcases h with h | h | h | h | h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 5 2 1 h).2
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 3 1 h).2

theorem lem13822_holds (h21 : Lem13821) (h16 : Lem13816) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
      ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ∀ W : Subgroup G, fsuV1 T V ≤ W → W < conjClosure S.V3 H →
        H ≤ Subgroup.normalizer (W : Set G) →
        (∃ k ∈ K, ∃ w ∈ W, k * w * k⁻¹ * w⁻¹ ∉ fsuV1 T V) →
        (∀ h ∈ H, (∀ w ∈ W, h * w * h⁻¹ * w⁻¹ ∈ fsuV1 T V) → h ∈ pCoreOf 2 H) ∧
        (∀ h ∈ H, (∀ u ∈ conjClosure S.V3 H, h * u * h⁻¹ * u⁻¹ ∈ W) → h ∈ pCoreOf 2 H) ∧
        (∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) ∧
        ∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
          F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) →
          F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H →
          mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
            mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) →
          (F8.A₁ (fsuV1 T V) (g : G) ≤ W ∧
              mIdx (conjClosure S.V3 H)
                  (centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))) ≤
                mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∧
              (mIdx (conjClosure S.V3 H)
                  (centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))) =
                  mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) →
                W ≤ F8.DH S.V3 (fsuV1 T V) H (g : G) ∧
                  ⁅W, F8.Uγ S.V3 H (g : G)⁆ ≤ F8.A₁ (fsuV1 T V) (g : G) ⊔ fsuV1 T V)) ∨
            (¬ F8.A₁ (fsuV1 T V) (g : G) ≤ W ∧
              mIdx W (centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))) ≤
                mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∧
              (mIdx W (centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))) =
                  mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) →
                W ⊔ F8.DH S.V3 (fsuV1 T V) H (g : G) = conjClosure S.V3 H ∧
                  ⁅conjClosure S.V3 H, F8.Uγ S.V3 H (g : G)⁆ ≤ F8.A₁ (fsuV1 T V) (g : G) ⊔ W)) := by
  intro G _ _ T L V S hS H hH K hK W hV1W hWU hHW hKW
  obtain ⟨-, hlist, ⟨hHKT, -⟩, hUK⟩ := h21 G T L V S hS H hH K hK
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hsimp := isSimpleGroup_of_list1821 hlist
  have hHK : H = K ⊔ T := hHKT.symm
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have hUHn : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hUH_H : conjClosure S.V3 H ≤ H :=
    hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hfW : ∀ h ∈ H, (∀ w ∈ W, h * w * h⁻¹ * w⁻¹ ∈ fsuV1 T V) → h ∈ pCoreOf 2 H :=
    fun h hh htr => S.mem_pCoreOf_of_trivial hS hH hKH hKn hHK hsimp hWU.le le_rfl hHW
      hF1.H_normalizes_V₁ hKW hh htr
  have hKU : ∃ k ∈ K, ∃ u ∈ conjClosure S.V3 H, k * u * k⁻¹ * u⁻¹ ∉ W := by
    by_contra hcon
    push Not at hcon
    apply hWU.not_ge
    rw [← hUK, Subgroup.commutator_le]
    intro u hu k hk
    have h1 := W.inv_mem (hcon k hk u hu)
    rwa [show (k * u * k⁻¹ * u⁻¹)⁻¹ = ⁅u, k⁆ by rw [commutatorElement_def]; group] at h1
  have hfU : ∀ h ∈ H, (∀ u ∈ conjClosure S.V3 H, h * u * h⁻¹ * u⁻¹ ∈ W) →
      h ∈ pCoreOf 2 H :=
    fun h hh htr => S.mem_pCoreOf_of_trivial hS hH hKH hKn hHK hsimp le_rfl hV1W hUHn hHW hKU
      hh htr
  refine ⟨hfW, hfU, ?_, ?_⟩
  ·
    rintro h hh ⟨hnt, c, hc⟩
    apply hnt
    have hQ : h ∈ pCoreOf 2 H := by
      by_cases hcW : ∀ u ∈ conjClosure S.V3 H, h * u * h⁻¹ * u⁻¹ ∈ W
      · exact hfU h hh hcW
      · push Not at hcW
        obtain ⟨u₁, hu₁, hu₁W⟩ := hcW
        have hcW' : c ∉ W := by
          intro hcw
          rcases hc u₁ hu₁ with h1 | h1
          · exact hu₁W (hV1W h1)
          · apply hu₁W
            have h2 := W.mul_mem (hV1W h1) hcw
            rwa [inv_mul_cancel_right] at h2
        refine hfW h hh fun w hw => ?_
        rcases hc w (hWU.le hw) with h1 | h1
        · exact h1
        · exfalso
          apply hcW'
          have hw' : h * w * h⁻¹ * w⁻¹ ∈ W :=
            W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHW hh) w).mp hw) (W.inv_mem hw)
          have h2 := W.mul_mem (W.inv_mem (hV1W h1)) hw'
          rwa [show (h * w * h⁻¹ * w⁻¹ * c⁻¹)⁻¹ * (h * w * h⁻¹ * w⁻¹) = c by group] at h2
    rw [hF1.pCoreOf_eq_centralizerMod] at hQ
    exact hQ.2.2
  ·
    intro γ γ' g s hDγ hDH hle
    have hUH2 : IsPGroup 2 (conjClosure S.V3 H) :=
      (pCoreOf_isPGroup 2 H).to_le hF1.conjClosure_Vp_le_pCoreOf
    have hW2 : IsPGroup 2 W := hUH2.to_le hWU.le
    have hDU : F8.DH S.V3 (fsuV1 T V) H (g : G) ≤ conjClosure S.V3 H :=
      centralizerMod_le_left _ _ _
    have hUγH : F8.Uγ S.V3 H (g : G) ≤ H := hF.Uγ_le_H s
    have hWuu : ∀ w ∈ W, ∀ u ∈ F8.Uγ S.V3 H (g : G), w * u * w⁻¹ * u⁻¹ ∈ W := by
      intro w hw u hu
      have h1 : u * w⁻¹ * u⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hHW (hUγH hu)) _).mp (W.inv_mem hw)
      rw [show w * u * w⁻¹ * u⁻¹ = w * (u * w⁻¹ * u⁻¹) by group]
      exact W.mul_mem hw h1
    by_cases hA : F8.A₁ (fsuV1 T V) (g : G) ≤ W
    · left
      have hDC : F8.DH S.V3 (fsuV1 T V) H (g : G) ≤
          centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)) :=
        fun d hd => ⟨hd.1, hHW (hUH_H hd.1), fun u hu => hA (hd.2.2 u hu)⟩
      have hWC : W ≤ centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)) :=
        fun w hw => ⟨hWU.le hw, hHW (hUH_H (hWU.le hw)), fun u hu => hWuu w hw u hu⟩
      have h1 := A6Gen.mIdx_le_of_le hUH2 hDC
      refine ⟨hA, h1.trans hle, fun heq => ?_⟩
      have h2 := A6Gen.mIdx_le_of_le hUH2
        (le_sup_left : F8.DH S.V3 (fsuV1 T V) H (g : G) ≤ F8.DH S.V3 (fsuV1 T V) H (g : G) ⊔ W)
      have h3 := A6Gen.mIdx_le_of_le hUH2 (sup_le hDC hWC)
      have h5 := A6Gen.eq_of_mIdx_eq hUH2 le_sup_left (sup_le hDU hWU.le) (by omega)
      have hWD : W ≤ F8.DH S.V3 (fsuV1 T V) H (g : G) := by
        rw [h5]
        exact le_sup_right
      refine ⟨hWD, ?_⟩
      rw [Subgroup.commutator_le]
      intro w hw u hu
      have h6 := (hWD hw).2.2 u hu
      rw [commutatorElement_def]
      exact Subgroup.mem_sup_left h6
    · right
      have hcA : Nat.card ↥(F8.A₁ (fsuV1 T V) (g : G)) = 2 := by
        rw [← hF1.card_V₁]
        exact Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective
      have hWA : W ⊓ F8.A₁ (fsuV1 T V) (g : G) = ⊥ := by
        by_contra hne
        apply hA
        refine le_of_card_eq_two_of_inf_ne_bot hcA ?_
        rwa [inf_comm]
      have hWDC : W ⊓ F8.DH S.V3 (fsuV1 T V) H (g : G) ≤
          centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G)) := by
        intro d hd
        refine ⟨hd.1, hF1.H_normalizes_V₁ (hUH_H (hWU.le hd.1)), fun u hu => ?_⟩
        have h1 : d * u * d⁻¹ * u⁻¹ ∈ W ⊓ F8.A₁ (fsuV1 T V) (g : G) :=
          ⟨hWuu d hd.1 u hu, hd.2.2.2 u hu⟩
        rw [hWA, Subgroup.mem_bot] at h1
        rw [h1]
        exact (fsuV1 T V).one_mem
      have h1 := A6Gen.mIdx_le_of_le hW2 hWDC
      have iW := HypF98.relIndex_eq_two_pow_mIdx
        (Y := W ⊓ F8.DH S.V3 (fsuV1 T V) H (g : G)) hW2
      have iU := HypF98.relIndex_eq_two_pow_mIdx
        (Y := F8.DH S.V3 (fsuV1 T V) H (g : G)) hUH2
      rw [Subgroup.inf_relIndex_left] at iW
      have hle2 : (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex W ≤
          (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex (conjClosure S.V3 H) :=
        Subgroup.relIndex_le_of_le_right hWU.le (relIndex_ne_zero' _ _)
      have h2 : mIdx W (W ⊓ F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
          mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) := by
        rw [iW, iU] at hle2
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle2
      refine ⟨hA, (h1.trans h2).trans hle, fun heq => ?_⟩
      have h3 : mIdx W (W ⊓ F8.DH S.V3 (fsuV1 T V) H (g : G)) =
          mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) := by omega
      have hsup : W ⊔ F8.DH S.V3 (fsuV1 T V) H (g : G) = conjClosure S.V3 H := by
        refine le_antisymm (sup_le hWU.le hDU) ?_
        have hm := Subgroup.relIndex_mul_relIndex (F8.DH S.V3 (fsuV1 T V) H (g : G))
          (W ⊔ F8.DH S.V3 (fsuV1 T V) H (g : G)) (conjClosure S.V3 H) le_sup_right
          (sup_le hWU.le hDU)
        have h4 : (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex W ≤
            (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex
              (W ⊔ F8.DH S.V3 (fsuV1 T V) H (g : G)) :=
          Subgroup.relIndex_le_of_le_right le_sup_left (relIndex_ne_zero' _ _)
        have h5 : (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex W =
            (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex (conjClosure S.V3 H) := by
          rw [iW, iU, h3]
        have hpos : 0 < (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex (conjClosure S.V3 H) :=
          Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
        have h6 : (W ⊔ F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex (conjClosure S.V3 H) = 1 := by
          nlinarith
        exact Subgroup.relIndex_eq_one.1 h6
      refine ⟨hsup, ?_⟩
      have hDW : F8.DH S.V3 (fsuV1 T V) H (g : G) ≤ Subgroup.normalizer (W : Set G) :=
        fun d hd => hHW (hUH_H hd.1)
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDW
      rw [Subgroup.commutator_le]
      intro u hu x hx
      have hu' : u ∈ ((F8.DH S.V3 (fsuV1 T V) H (g : G) ⊔ W : Subgroup G) : Set G) := by
        rw [sup_comm, hsup]
        exact hu
      rw [hset] at hu'
      obtain ⟨d, hd, w, hw, hdw⟩ := hu'
      have hdw' : d * w = u := hdw
      rw [← hdw', commutatorElement_def]
      have e : d * w * x * (d * w)⁻¹ * x⁻¹ =
          (d * (w * x * w⁻¹ * x⁻¹) * d⁻¹) * (d * x * d⁻¹ * x⁻¹) := by group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left (hd.2.2 x hx))
      exact (Subgroup.mem_normalizer_iff.mp (hDW hd) _).mp (hWuu w hw x hx)

theorem lem13823_holds (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
      ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ∀ W : Subgroup G, fsuV1 T V ≤ W → W < conjClosure S.V3 H →
        H ≤ Subgroup.normalizer (W : Set G) →
        (∃ k ∈ K, ∃ w ∈ W, k * w * k⁻¹ * w⁻¹ ∉ fsuV1 T V) →
        ∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
          F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) →
          F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H →
          mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
            mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) →
          mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 →
          (mIdx W (centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))) = 1 ∧
            mIdx (conjClosure S.V3 H)
              (centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))) = 1 ∧
            mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) = 1 ∧
            mIdx (F8.DH S.V3 (fsuV1 T V) H (g : G))
              (conjClosure S.V3 H ⊓ Subgroup.centralizer (F8.Uγ S.V3 H (g : G) : Set G)) = 1 ∧
            (conjClosure S.V3 H ⊓ Subgroup.centralizer (F8.Uγ S.V3 H (g : G) : Set G)) ⊔ W =
              centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))) ∧
          1 < mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) ∧
          ((¬ F8.A₁ (fsuV1 T V) (g : G) ≤ W ∧
              ∀ w ∈ centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G)),
                ∀ v ∈ F8.Uγ V H (g : G), v * w * v⁻¹ * w⁻¹ ∈ fsuV1 T V) ∨
            (F8.A₁ (fsuV1 T V) (g : G) ≤ W ∧
              ∀ u ∈ centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)),
                ∀ v ∈ F8.Uγ V H (g : G), v * u * v⁻¹ * u⁻¹ ∈ W)) := by
  intro G _ _ T L V S hS H hH K hK W hV1W hWU hHW hKW γ γ' g s hDγ hDH hle hm1
  obtain ⟨hfW, hfU, hnt, -⟩ := lem13822_holds h21 h16 G T L V S hS H hH K hK W hV1W hWU hHW hKW
  obtain ⟨hL1K, -, ⟨hHKT, -⟩, -⟩ := h21 G T L V S hS H hH K hK
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have hUH_H : conjClosure S.V3 H ≤ H := hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hUγH : F8.Uγ S.V3 H (g : G) ≤ H := hF.Uγ_le_H s
  have hUH2 : IsPGroup 2 (conjClosure S.V3 H) :=
    (pCoreOf_isPGroup 2 H).to_le hF1.conjClosure_Vp_le_pCoreOf
  have hW2 : IsPGroup 2 W := hUH2.to_le hWU.le
  have hDU : F8.DH S.V3 (fsuV1 T V) H (g : G) ≤ conjClosure S.V3 H := centralizerMod_le_left _ _ _
  have hDH2 : IsPGroup 2 (F8.DH S.V3 (fsuV1 T V) H (g : G)) := hUH2.to_le hDU
  have hDQ := hF.Dγ_eq_inf_pCoreOf s
  set CU := centralizerMod (fsuV1 T V) (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)) with hCU
  set CUh := centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)) with hCUh
  set CW := centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G)) with hCW
  set CH := conjClosure S.V3 H ⊓ Subgroup.centralizer (F8.Uγ S.V3 H (g : G) : Set G) with hCH
  have hCUU : CU ≤ conjClosure S.V3 H := centralizerMod_le_left _ _ _
  have hCUhU : CUh ≤ conjClosure S.V3 H := centralizerMod_le_left _ _ _
  obtain ⟨x, hxU, hxD⟩ := IsConcreteLE.exists_of_lt hDγ
  have hxQ : x ∉ pCoreOf 2 H := fun hq => hxD (by rw [hDQ]; exact ⟨hxU, hq⟩)
  have hpos : 0 < mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) := by omega
  obtain ⟨hq, -⟩ := hF.F916_2_aux s hpos hle
  have hU2 : IsPGroup 2 (F8.Uγ S.V3 H (g : G)) := isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have hiD : (F8.Dγ S.V3 (fsuV1 T V) H (g : G)).relIndex (F8.Uγ S.V3 H (g : G)) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hU2, hm1, pow_one]
  have hCU2 : mIdx (conjClosure S.V3 H) CU ≤ 2 := by
    have h1 := hq.2.2.2.2
    rw [← hDQ, hiD, HypF98.relIndex_eq_two_pow_mIdx hUH2] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hCW1 : 1 ≤ mIdx W CW := by
    by_contra h0
    push Not at h0
    have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := CW) hW2
    rw [show mIdx W CW = 0 by omega, pow_zero, Subgroup.relIndex_eq_one] at h1
    apply hxQ
    refine hfW x (hUγH hxU) fun w hw => ?_
    have h2 := (fsuV1 T V).inv_mem ((h1 hw).2.2 x hxU)
    rwa [show (w * x * w⁻¹ * x⁻¹)⁻¹ = x * w * x⁻¹ * w⁻¹ by group] at h2
  have hCUh1 : 1 ≤ mIdx (conjClosure S.V3 H) CUh := by
    by_contra h0
    push Not at h0
    have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := CUh) hUH2
    rw [show mIdx (conjClosure S.V3 H) CUh = 0 by omega, pow_zero, Subgroup.relIndex_eq_one] at h1
    apply hxQ
    refine hfU x (hUγH hxU) fun u hu => ?_
    have h2 := W.inv_mem ((h1 hu).2.2 x hxU)
    rwa [show (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ by group] at h2
  have hCWeq : CU ⊓ W = CW := by
    ext w
    constructor
    · rintro ⟨⟨-, hwN, hwc⟩, hw⟩
      exact ⟨hw, hwN, hwc⟩
    · rintro ⟨hw, hwN, hwc⟩
      exact ⟨⟨hWU.le hw, hwN, hwc⟩, hw⟩
  have hCUW : CU ⊔ W ≤ CUh := by
    refine sup_le (fun u hu => ⟨hu.1, hHW (hUH_H hu.1), fun y hy => hV1W (hu.2.2 y hy)⟩)
      (fun w hw => ⟨hWU.le hw, hHW (hUH_H (hWU.le hw)), fun y hy => ?_⟩)
    have h1 : y * w⁻¹ * y⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hHW (hUγH hy)) _).mp (W.inv_mem hw)
    rw [show w * y * w⁻¹ * y⁻¹ = w * (y * w⁻¹ * y⁻¹) by group]
    exact W.mul_mem hw h1
  have hadd : mIdx W CW + mIdx (conjClosure S.V3 H) CUh ≤ mIdx (conjClosure S.V3 H) CU := by
    have h1 : CU.relIndex W ≤ CU.relIndex (CU ⊔ W) :=
      Subgroup.relIndex_le_of_le_right le_sup_right (relIndex_ne_zero' _ _)
    have h2 := Subgroup.relIndex_mul_relIndex CU (CU ⊔ W) (conjClosure S.V3 H) le_sup_left
      (sup_le hCUU hWU.le)
    have h3 : CUh.relIndex (conjClosure S.V3 H) ≤ (CU ⊔ W).relIndex (conjClosure S.V3 H) :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (relIndex_ne_zero' _ _))
        (Subgroup.relIndex_dvd_of_le_left (L := conjClosure S.V3 H) hCUW)
    have h4 : CU.relIndex W = 2 ^ mIdx W CW := by
      rw [← Subgroup.inf_relIndex_right, hCWeq]
      exact HypF98.relIndex_eq_two_pow_mIdx hW2
    rw [h4] at h1
    rw [HypF98.relIndex_eq_two_pow_mIdx (Y := CUh) hUH2] at h3
    rw [HypF98.relIndex_eq_two_pow_mIdx (Y := CU) hUH2] at h2
    have h5 : 2 ^ mIdx W CW * 2 ^ mIdx (conjClosure S.V3 H) CUh ≤
        2 ^ mIdx (conjClosure S.V3 H) CU := by
      rw [← h2]
      exact Nat.mul_le_mul h1 h3
    rw [← pow_add] at h5
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h5
  have hmW : mIdx W CW = 1 := by omega
  have hmUh : mIdx (conjClosure S.V3 H) CUh = 1 := by omega
  have hmU : mIdx (conjClosure S.V3 H) CU = 2 := by omega
  have hmD : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) = 1 :=
    (S.lemma13_8_10 hF s hle hm1 hDH).1
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hUst : conjClosure S.V3 H ≤ stab γ :=
    (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans
      inf_le_right))
  have hstN : stab γ ≤ Subgroup.normalizer (F8.A₁ (fsuV1 T V) (g : G) : Set G) := by
    rw [hstab]
    exact conjSub_le_normalizer hF1.H_normalizes_V₁
  have hCHD : CH ≤ F8.DH S.V3 (fsuV1 T V) H (g : G) := by
    rintro c ⟨hcU, hcC⟩
    refine ⟨hcU, hstN (hUst hcU), fun u hu => ?_⟩
    rw [← Subgroup.mem_centralizer_iff.mp hcC u hu, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hCHle := S.relIndex_CH_le hS hH s hm1 hxU hxD
  have hmCH : mIdx (F8.DH S.V3 (fsuV1 T V) H (g : G)) CH ≤ 1 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hDH2] at hCHle
    have : 2 ^ mIdx (F8.DH S.V3 (fsuV1 T V) H (g : G)) CH ≤ 2 ^ 1 := by simpa using hCHle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hCHCU : CH ≤ CU := by
    rintro c ⟨hcU, hcC⟩
    refine ⟨hcU, hF1.H_normalizes_V₁ (hUH_H hcU), fun u hu => ?_⟩
    rw [← Subgroup.mem_centralizer_iff.mp hcC u hu, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hmCHU : mIdx (conjClosure S.V3 H) CH =
      mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) +
        mIdx (F8.DH S.V3 (fsuV1 T V) H (g : G)) CH := by
    have h1 := Subgroup.relIndex_mul_relIndex CH (F8.DH S.V3 (fsuV1 T V) H (g : G))
      (conjClosure S.V3 H) hCHD hDU
    rw [HypF98.relIndex_eq_two_pow_mIdx hDH2, HypF98.relIndex_eq_two_pow_mIdx hUH2,
      HypF98.relIndex_eq_two_pow_mIdx hUH2, ← pow_add] at h1
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  have hmCH2 : mIdx (conjClosure S.V3 H) CU ≤ mIdx (conjClosure S.V3 H) CH :=
    A6Gen.mIdx_le_of_le hUH2 hCHCU
  have hmCH1 : mIdx (F8.DH S.V3 (fsuV1 T V) H (g : G)) CH = 1 := by omega
  have hCHeq : CH = CU := A6Gen.eq_of_mIdx_eq hUH2 hCHCU hCUU (by omega)
  have hCHW : CH ⊔ W = CUh := by
    rw [hCHeq]
    refine A6Gen.eq_of_mIdx_eq hUH2 hCUW hCUhU ?_
    have h1 := A6Gen.mIdx_le_of_le hUH2 hCUW
    have h2 : mIdx (conjClosure S.V3 H) (CU ⊔ W) ≤ 1 := by
      have h3 : CU.relIndex W ≤ CU.relIndex (CU ⊔ W) :=
        Subgroup.relIndex_le_of_le_right le_sup_right (relIndex_ne_zero' _ _)
      have h4 := Subgroup.relIndex_mul_relIndex CU (CU ⊔ W) (conjClosure S.V3 H) le_sup_left
        (sup_le hCUU hWU.le)
      have h5 : CU.relIndex W = 2 := by
        rw [← Subgroup.inf_relIndex_right, hCWeq, HypF98.relIndex_eq_two_pow_mIdx hW2, hmW,
          pow_one]
      rw [HypF98.relIndex_eq_two_pow_mIdx hUH2, HypF98.relIndex_eq_two_pow_mIdx hUH2, hmU] at h4
      rw [h5] at h3
      have h6 : 2 ^ mIdx (conjClosure S.V3 H) (CU ⊔ W) ≤ 2 ^ 1 := by
        nlinarith [Nat.one_le_two_pow (n := mIdx (conjClosure S.V3 H) (CU ⊔ W))]
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h6
    omega
  have hHK' : H = K ⊔ (S.L1 ⊔ T) := by
    rw [← sup_assoc, sup_eq_left.2 hL1K, hHKT]
  have h2 := lem13818Four_holds h36 h139 h1334 h13 h13314 h13315 h1356two G T L V S hS H hH K hK
    hKn hHK' hnt γ γ' g s hDγ hDH hle
  refine ⟨⟨hmW, hmUh, hmD, hmCH1, hCHW⟩, h2, ?_⟩
  have hVC : ∀ c ∈ CH, ∀ v ∈ F8.Uγ V H (g : G), v * c * v⁻¹ * c⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) :=
    fun c hc v hv => S.comm_mem_A₁_of_cent hS h13315 h1356two hH s hc.1
      (fun y hy => Subgroup.mem_centralizer_iff.mp hc.2 y hy) hv
  have hVγH : F8.Uγ V H (g : G) ≤ H := hF.Vγ_le_H s
  by_cases hA : F8.A₁ (fsuV1 T V) (g : G) ≤ W
  · right
    refine ⟨hA, fun u hu v hv => ?_⟩
    rw [← hCHW] at hu
    have hWn : CH ≤ Subgroup.normalizer (W : Set G) := fun c hc => hHW (hUH_H hc.1)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right CH W hWn
    have hu' : u ∈ ((CH ⊔ W : Subgroup G) : Set G) := hu
    rw [hset] at hu'
    obtain ⟨c, hc, w, hw, rfl⟩ := hu'
    have h1 := hA (hVC c hc v hv)
    have h2 : v * w * v⁻¹ * w⁻¹ ∈ W := by
      have h3 : v * w * v⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hHW (hVγH hv)) w).mp hw
      exact W.mul_mem h3 (W.inv_mem hw)
    have e : v * (c * w) * v⁻¹ * (c * w)⁻¹ =
        (v * c * v⁻¹ * c⁻¹) * (c * (v * w * v⁻¹ * w⁻¹) * c⁻¹) := by group
    rw [e]
    exact W.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp (hWn hc) _).mp h2)
  · left
    refine ⟨hA, fun w hw v hv => ?_⟩
    have hcA : Nat.card ↥(F8.A₁ (fsuV1 T V) (g : G)) = 2 := by
      rw [← hF1.card_V₁]
      exact Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective
    have hWA : W ⊓ F8.A₁ (fsuV1 T V) (g : G) = ⊥ := by
      by_contra hne
      apply hA
      refine le_of_card_eq_two_of_inf_ne_bot hcA ?_
      rwa [inf_comm]
    have hw' : w ∈ CU ⊓ W := by rw [hCWeq]; exact hw
    have hwC : w ∈ CH := by rw [hCHeq]; exact hw'.1
    have h1 := hVC w hwC v hv
    have h2 : v * w * v⁻¹ * w⁻¹ ∈ W := by
      have h3 : v * w * v⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hHW (hVγH hv)) w).mp hw'.2
      exact W.mul_mem h3 (W.inv_mem hw'.2)
    have h4 : v * w * v⁻¹ * w⁻¹ ∈ W ⊓ F8.A₁ (fsuV1 T V) (g : G) := ⟨h2, h1⟩
    rw [hWA, Subgroup.mem_bot] at h4
    rw [h4]
    exact (fsuV1 T V).one_mem

end CFSG.Quasithin.H13.A6
