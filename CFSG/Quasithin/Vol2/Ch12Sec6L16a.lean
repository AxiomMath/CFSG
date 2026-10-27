module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2A8
public import CFSG.Quasithin.Vol2.Ch12Sec6T2J

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

theorem eq_conj_A6s_of_hom {B : Type*} [Group B] [Finite B]
    (hB : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = (⊤ : Subgroup B))
    (ψ : B →* Equiv.Perm (Fin 8)) (hψ : IsPGroup 2 ↥ψ.ker) (φ : B →* ↥A6s)
    (hφ : Function.Surjective φ) (hk : IsPGroup 2 ↥φ.ker) :
    ∃ τ ∈ alternatingGroup (Fin 8), ψ.range = A6s.map (MulAut.conj τ).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ψ.ker ≤ φ.ker := by
    set M := (ψ.ker.map φ).map A6s.subtype with hM
    have hMA : M ≤ A6s := Subgroup.map_subtype_le _
    have hMn : ∀ a ∈ A6s, ∀ m ∈ M, a * m * a⁻¹ ∈ M := by
      intro a ha m hm
      obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hm
      obtain ⟨c, hc⟩ := hφ ⟨a, ha⟩
      refine ⟨φ (c * b * c⁻¹), ⟨c * b * c⁻¹, ψ.normal_ker.conj_mem b hb c, rfl⟩, ?_⟩
      simp [hc]
    have hM2 : IsPGroup 2 ↥M := (hψ.map φ).map _
    have hMb := eq_bot_of_normal hMA hMn hM2
    intro b hb
    have : (φ b : Equiv.Perm (Fin 8)) ∈ M := ⟨φ b, ⟨b, hb, rfl⟩, rfl⟩
    rw [hMb, Subgroup.mem_bot] at this
    exact Subtype.ext this
  set X := ψ.range with hX
  set K : Subgroup ↥X := φ.ker.map ψ.rangeRestrict with hK
  have : K.Normal := φ.normal_ker.map ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hK2 : IsPGroup 2 ↥K := hk.map _
  have hXp : ⁅X, X⁆ = X := by
    rw [hX, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hB]
  have hcard : Nat.card X = 360 * Nat.card K := by
    have h1 : Nat.card B = Nat.card X * Nat.card ψ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    have h2 : Nat.card B = 360 * Nat.card φ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, card_A6s]
    have h3 : Nat.card φ.ker = Nat.card K * Nat.card ψ.ker := by
      let r : ↥φ.ker →* ↥X := ψ.rangeRestrict.comp φ.ker.subtype
      have hrr : r.range = K := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
      have hrk : r.ker = ψ.ker.subgroupOf φ.ker := by
        ext x
        simp only [r, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
          Subgroup.mem_subgroupOf]
        rw [← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup r.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv, hrr, hrk,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    rw [h3] at h2
    rw [h1] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h2]; ring)
  exact eq_conj_A6s hXp hK2 hcard

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem map_conj_Gv (g v : G) :
    (Gv v).map (MulAut.conj g).toMonoidHom = Gv (g * v * g⁻¹) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    show g * y * g⁻¹ ∈ Subgroup.centralizer {g * v * g⁻¹}
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * (g * v * g⁻¹) = g * (y * v) * g⁻¹ := by group
      _ = g * (v * y) * g⁻¹ := by rw [hy']
      _ = g * v * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [Gv, Subgroup.mem_centralizer_singleton_iff] at hx
    show g⁻¹ * x * g ∈ Subgroup.centralizer {v}
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * v = g⁻¹ * (x * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * x) * g := by rw [hx]
      _ = v * (g⁻¹ * x * g) := by group

omit [Finite G] [IsMulCommutative ↥V] in
theorem map_conj_oThreePrimeResidual (g : G) (X : Subgroup G) :
    (oThreePrimeResidual X).map (MulAut.conj g).toMonoidHom =
      oThreePrimeResidual (X.map (MulAut.conj g).toMonoidHom) := by
  rw [oThreePrimeResidual, oThreePrimeResidual, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxX, k, hk⟩, rfl⟩
    exact ⟨⟨x, hxX, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨⟨x, hxX, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hxX, k, ?_⟩, rfl⟩
    rw [← map_pow] at hk
    exact (MulEquiv.map_eq_one_iff (MulAut.conj g)).1 hk

omit [Finite G] [IsMulCommutative ↥V] in
theorem map_conj_self {L : Subgroup G} {l : G} (hl : l ∈ L) :
    L.map (MulAut.conj l).toMonoidHom = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact L.mul_mem (L.mul_mem hl hy) (L.inv_mem hl)
  · intro hx
    refine ⟨l⁻¹ * x * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

omit [IsMulCommutative ↥V] in
theorem Lv_conj {l : G} (hl : l ∈ L) (v : G) :
    Lv L (l * v * l⁻¹) = (Lv L v).map (MulAut.conj l).toMonoidHom := by
  have h1 : L ⊓ Gv (l * v * l⁻¹) = (L ⊓ Gv v).map (MulAut.conj l).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj l).injective, map_conj_self hl, map_conj_Gv]
  rw [Lv, Lv, h1, map_perfectCore]

omit [IsMulCommutative ↥V] in
theorem centralizer_le_M (h331 : Stmt3_3_1) (hH : Hyp126 G T L V) {w : G}
    (hwT : w ∈ Subgroup.centralizer (T : Set G)) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1)
    (hLw : L ≤ Subgroup.centralizer ({w} : Set G)) :
    Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have hCN : Subgroup.centralizer ({w} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
  have hTw : T ≤ Subgroup.centralizer ({w} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hwT t ht
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one]; exact orderOf_eq_prime hw2 hw1)
  have hP1 : Subgroup.zpowers w ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hw1
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨Subgroup.zpowers w, hP1, hP2, rfl⟩ : IsTwoLocal _)
  rw [← huniq M' hM' ((sup_le hLw hTw).trans (hCN.trans hle))]
  exact hCN.trans hle

theorem le_of_psi_le (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {A B : Subgroup G} (hBL : B ≤ L) (hBp : ⁅B, B⁆ = B)
    (hAn : L ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (A : Set G))
    (hle : (B.subgroupOf L).map (psiP F hH) ≤ (A.subgroupOf L).map (psiP F hH)) : B ≤ A := by
  have hdec : ∀ b ∈ B, ∃ a ∈ A, a⁻¹ * b ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := hle ⟨⟨b, hBL hb⟩, hb, rfl⟩
    refine ⟨a, ha, L.mul_mem (L.inv_mem a.2) (hBL hb), ?_⟩
    have hq : S126L19a.psi F hH (a⁻¹ * ⟨b, hBL hb⟩) = 1 := by
      apply Subtype.ext
      have : psiP F hH (a⁻¹ * ⟨b, hBL hb⟩) = 1 := by
        rw [map_mul, map_inv, hab, inv_mul_cancel]
      exact this
    exact (S126L19a.psi_eq_one_iff F hH _).1 hq
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    obtain ⟨a, ha, hn⟩ := hdec b hb
    have e : b = a * (a⁻¹ * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ha) (hAn hn)
  refine le_of_two_mod hBp hBN fun b hb => ?_
  obtain ⟨a, ha, hn⟩ := hdec b hb
  obtain ⟨k, hk⟩ := isPGroup_CL h1222 hH ⟨_, hn⟩
  refine ⟨a, ha, a⁻¹ * b, by group, hAn hn, k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem actsAs_of_mem_centralizerSection (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {y : G} (hy : y ∈ centralizerSection (L ⊔ T) (Lv L v) (pCoreOf 2 (Lv L v))) :
    ∃ σ : Equiv.Perm (Fin 8), ActsAs F y σ ∧ (σ = 1 ∨ σ = Equiv.swap 0 1) := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  obtain ⟨hyX, -, -, hyc⟩ := hy
  obtain ⟨σ, hσ⟩ := exists_actsAs F hH (hXL hyX) (hXV hyX)
  refine ⟨σ, hσ, eq_of_comm fun a ha => ?_⟩
  obtain ⟨l, hl, rfl⟩ := exists_Lv_of_A6s h1222 F hH hv hβ a ha
  have hc := hyc l hl
  have hcL : (l : G) * y * (l : G)⁻¹ * y⁻¹ ∈ L := Lv_le_L L v (pCoreOf_le 2 _ hc)
  have h1 : psiP F hH ⟨_, hcL⟩ = 1 := psi_pCore_eq_one h1222 F hH hv hβ hc
  have hact1 := (actsAs_psiP F hH l).commutator hσ (hLV l.2) (hXV hyX)
  have hact2 : ActsAs F ((l : G) * y * (l : G)⁻¹ * y⁻¹) 1 := by
    have := actsAs_psiP F hH ⟨_, hcL⟩
    rwa [h1] at this
  have e := hact1.unique hact2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (hLV l.2) (hXV hyX)) (Subgroup.inv_mem _ (hLV l.2))) (Subgroup.inv_mem _ (hXV hyX)))
  calc σ * psiP F hH l
      = (psiP F hH l * σ * (psiP F hH l)⁻¹ * σ⁻¹)⁻¹ * (psiP F hH l * σ) := by group
    _ = psiP F hH l * σ := by rw [e, inv_one, one_mul]

theorem centralizerSection_le_Rv (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    centralizerSection (L ⊔ T) (Lv L v) (pCoreOf 2 (Lv L v)) ≤ Rv T L v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizerSection (L ⊔ T) (Lv L v) (pCoreOf 2 (Lv L v)) with hY
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hact : ∀ y ∈ Y, ∃ σ : Equiv.Perm (Fin 8), ActsAs F y σ ∧
      (σ = 1 ∨ σ = Equiv.swap 0 1) := fun y hy =>
    actsAs_of_mem_centralizerSection h1222 F hH hv hβ hy
  have hYC : Y ≤ (L ⊔ T) ⊓ Gv v := by
    intro y hy
    obtain ⟨σ, hσ, h1⟩ := hact y hy
    refine ⟨hy.1, (mem_Gv_iff h1222 F hH hv hβ (hXL hy.1) (hXV hy.1) hσ).2 ?_⟩
    rcases h1 with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨by decide, by decide⟩
  have hY2 : IsPGroup 2 ↥Y := by
    intro y
    obtain ⟨σ, hσ, h1⟩ := hact y y.2
    have hσ2 : σ * σ = 1 := by
      rcases h1 with rfl | rfl
      · exact mul_one 1
      · exact Equiv.swap_mul_self 0 1
    have hyX : (y : G) ∈ L ⊔ T := y.2.1
    have hyy : ActsAs F ((y : G) * y) 1 := by
      have := hσ.mul hσ (hXV hyX)
      rwa [hσ2] at this
    have hyyX : (y : G) * y ∈ L ⊔ T := (L ⊔ T).mul_mem hyX hyX
    have hyyC : (y : G) * y ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨hyyX, mem_centralizer_of_actsAs_one F hVL hLV (hXL hyyX) (hXV hyyX) hyy⟩
    obtain ⟨n, hn⟩ := isPGroup_CLT_V h1222 hH ⟨_, hyyC⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have h2 : ((y : G) * y) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    rw [← sq, ← pow_mul, ← pow_succ'] at h2
    simpa using h2
  have hCN : (L ⊔ T) ⊓ Gv v ≤ Subgroup.normalizer (Lv L v : Set G) := by
    refine le_trans ?_ (normalizer_le_normalizer_perfectCore (L ⊓ Gv v))
    refine (le_inf (inf_le_left.trans hXL) ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (inf_le_right : (L ⊔ T) ⊓ Gv v ≤ Gv v).trans Subgroup.le_normalizer
  have hCY : (L ⊔ T) ⊓ Gv v ≤ Subgroup.normalizer (Y : Set G) := by
    intro c hc
    have key : ∀ d ∈ (L ⊔ T) ⊓ Gv v, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y := fun d hd y hy =>
      conj_mem_centralizerSection (Subgroup.le_normalizer hd.1) (hCN hd)
        (normalizer_le_normalizer_pCoreOf 2 _ (hCN hd)) hy
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key c hc y hy, fun hy => ?_⟩
    have := key c⁻¹ (Subgroup.inv_mem _ hc) _ hy
    simpa [mul_assoc] using this
  exact le_pCoreOf_of_le_normalizer 2 hYC hCY hY2

end S126T2

end CFSG.Quasithin.H13
