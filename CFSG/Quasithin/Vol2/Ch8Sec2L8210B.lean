module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsB
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch7Elim

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8210B

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuV_le_of_82 (hyp : Hyp7_0_2 G T L I) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hVT : fsuV T I ≤ T) : fsuV T I ≤ L := by
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  obtain ⟨-, -, -, hIX, -⟩ := hyp.fsu.irrPlus
  have hcl : conjClosure L T = L := hL0
  rw [hcl] at hIX
  have hIT : I ≤ T := (le_fsuV I T).trans hVT
  have hIL : I ≤ L := by
    rw [← hIX, Subgroup.commutator_le]
    intro i hi l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL (hIT hi)) l).mp hl) (L.inv_mem hl)
  exact conjClosure_le fun t ht x hx => (Subgroup.mem_normalizer_iff.mp (hTL ht) x).mp (hIL hx)

theorem pCoreOf_le_T_of_82 (hyp : Hyp7_0_2 G T L I) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hp : IsPGroup 2 ↥(pCoreOf 2 L ⊔ T) :=
    IsPGroup.to_sup_of_normal_left' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      hyp.fsu.sylow.1 hTQ
  let S : Sylow 2 G := hyp.fsu.sylow.1.toSylow hyp.fsu.sylow.2
  have hS : (S : Subgroup G) = T := rfl
  have h2 : (S : Subgroup G) ≤ pCoreOf 2 L ⊔ T := by
    rw [hS]
    exact le_sup_right
  have h3 := S.is_maximal' hp h2
  calc pCoreOf 2 L ≤ pCoreOf 2 L ⊔ T := le_sup_left
    _ = S := h3
    _ = T := hS

theorem pCoreOf_le_centralizer_of_82 (hsimp : HSimple82) {V : Subgroup G}
    [hc : IsMulCommutative ↥V] (hmod : IsModel82 (V := ↥V) (autOn L V))
    (hLN : L ≤ Subgroup.normalizer (V : Set G)) :
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, a, b, hab⟩ := hsimp ↥V (autOn L V) hmod
  have hQL : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hNH : autOn (pCoreOf 2 L) V ≤ autOn L V := Subgroup.map_mono fun x hx => hQL hx
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hnorm : ((autOn (pCoreOf 2 L) V).subgroupOf (autOn L V)).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨q, hq, hqe⟩ := hn
    obtain ⟨l, hl, hle⟩ := h.2
    have hq' : (q : G) ∈ pCoreOf 2 L := hq
    have hl' : (l : G) ∈ L := hl
    refine ⟨l * q * l⁻¹, ?_, ?_⟩
    · show ((l * q * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 L
      have := (Subgroup.mem_normalizer_iff.mp (hLQ hl') q).mp hq'
      simpa using this
    · rw [map_mul, map_mul, map_inv, hqe, hle]
      rfl
  have hNp : IsPGroup 2 ↥(autOn (pCoreOf 2 L) V) := by
    have h1 : IsPGroup 2 ↥((pCoreOf 2 L).subgroupOf (Subgroup.normalizer (V : Set G))) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).of_equiv
        (Subgroup.subgroupOfEquivOfLe (hQL.trans hLN)).symm
    exact h1.map _
  have := hnorm
  rcases hS.eq_bot_or_eq_top_of_normal ((autOn (pCoreOf 2 L) V).subgroupOf (autOn L V)) with h | h
  · intro q hq
    have hqN : q ∈ Subgroup.normalizer (V : Set G) := hLN (hQL hq)
    have hmem : conjAct V ⟨q, hqN⟩ ∈ autOn (pCoreOf 2 L) V :=
      ⟨⟨q, hqN⟩, (hq : ((⟨q, hqN⟩ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 L),
        rfl⟩
    have hmemH : conjAct V ⟨q, hqN⟩ ∈ autOn L V := hNH hmem
    have h1 : (⟨conjAct V ⟨q, hqN⟩, hmemH⟩ : ↥(autOn L V)) ∈
        (autOn (pCoreOf 2 L) V).subgroupOf (autOn L V) := by
      rw [Subgroup.mem_subgroupOf]
      exact hmem
    rw [h, Subgroup.mem_bot] at h1
    have h2 : conjAct V ⟨q, hqN⟩ = 1 := congrArg Subtype.val h1
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h3 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h2
    simp only [CFSG.QuasithinUnique.Setup.coe_conjAct_apply, MulAut.one_apply] at h3
    calc v * q = (q * v * q⁻¹) * q := by rw [h3]
      _ = q * v := by group
  · exfalso
    have hHp : IsPGroup 2 ↥(autOn L V) := by
      intro x
      have hx : x ∈ (autOn (pCoreOf 2 L) V).subgroupOf (autOn L V) := by
        rw [h]
        exact Subgroup.mem_top x
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨k, hk⟩ := hNp ⟨x, hx⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have : Nontrivial ↥(autOn L V) := ⟨⟨a * b, b * a, hab⟩⟩
    have hcen : Nontrivial ↥(Subgroup.center ↥(autOn L V)) := hHp.center_nontrivial
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(autOn L V)) with hc0 | hc0
    · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hcen
      rw [hc0, Subgroup.mem_bot] at hx hy
      exact hxy (Subtype.ext (hx.trans hy.symm))
    · exact hab (Subgroup.mem_center_iff.mp (hc0 ▸ Subgroup.mem_top b) a)

omit [Finite G] in
theorem mem_sup_of_le_normalizer_82 {V A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) {z : G} (hz : z ∈ V ⊔ A) :
    ∃ v ∈ V, ∃ a ∈ A, z = v * a := by
  let S : Subgroup G :=
    { carrier := {x | ∃ v ∈ V, ∃ a ∈ A, x = v * a}
      one_mem' := ⟨1, V.one_mem, 1, A.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨v₁, hv₁, a₁, ha₁, rfl⟩ ⟨v₂, hv₂, a₂, ha₂, rfl⟩
        have hn : a₁ * v₂ * a₁⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hA ha₁) v₂).1 hv₂
        refine ⟨v₁ * (a₁ * v₂ * a₁⁻¹), V.mul_mem hv₁ hn, a₁ * a₂, A.mul_mem ha₁ ha₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨v, hv, a, ha, rfl⟩
        have hn : a⁻¹ * v⁻¹ * a ∈ V := by
          have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem ha)) v⁻¹).1 (V.inv_mem hv)
          simpa using this
        refine ⟨a⁻¹ * v⁻¹ * a, hn, a⁻¹, A.inv_mem ha, ?_⟩
        group }
  have hle : V ⊔ A ≤ S := sup_le (fun v hv => ⟨v, hv, 1, A.one_mem, (mul_one v).symm⟩)
    (fun a ha => ⟨1, V.one_mem, a, ha, (one_mul a).symm⟩)
  exact hle hz

omit [Finite G] in
theorem commutator_pCoreOf_le_of_82 {V A Q : Subgroup G} (hQT : Q ≤ T)
    (hQC : Q ≤ Subgroup.centralizer (V : Set G)) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hAT : A ≤ T) (hTVA : T ≤ Subgroup.normalizer ((V ⊔ A : Subgroup G) : Set G))
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hVC : V ≤ Subgroup.centralizer (V : Set G))
    (hAC : A ⊓ Subgroup.centralizer (V : Set G) ≤ V) : ⁅Q, A⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro q hq a ha
  have hx1 : ⁅q, a⁆ ∈ Q := by
    rw [commutatorElement_def]
    have h1 : a * q⁻¹ * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hTQ (hAT ha)) q⁻¹).mp (Q.inv_mem hq)
    have := Q.mul_mem hq h1
    simpa [mul_assoc] using this
  have hx2 : ⁅q, a⁆ ∈ V ⊔ A := by
    rw [commutatorElement_def]
    have ha' : a ∈ V ⊔ A := le_sup_right (a := V) ha
    have h1 : q * a * q⁻¹ ∈ V ⊔ A := (Subgroup.mem_normalizer_iff.mp (hTVA (hQT hq)) a).mp ha'
    exact (V ⊔ A).mul_mem h1 ((V ⊔ A).inv_mem ha')
  obtain ⟨v, hv, a', ha', he⟩ := mem_sup_of_le_normalizer_82 hAN hx2
  have ha'C : a' ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : v⁻¹ * ⁅q, a⁆ ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem (hVC hv)) (hQC hx1)
    rw [he] at h1
    simpa using h1
  rw [he]
  exact V.mul_mem hv (hAC ⟨ha', ha'C⟩)

omit [Finite G] in

omit [Finite G] in
theorem sup_pCoreOf_eq_or_commutator_le_of_82 (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {N : Subgroup G} (hNL : N ≤ L) (hLN : L ≤ Subgroup.normalizer (N : Set G)) :
    N ⊔ pCoreOf 2 L = L ∨ ⁅N, L⁆ ≤ pCoreOf 2 L := by
  have hnorm : (N.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLN
  set f := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hmn : ((N.subgroupOf L).map f).Normal := hnorm.map f (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hmn with h | h
  · left
    apply le_antisymm (sup_le hNL (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_map.mp (h ▸ Subgroup.mem_top (f ⟨x, hx⟩) :
      f ⟨x, hx⟩ ∈ (N.subgroupOf L).map f))
    have hker : y⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker, map_mul, map_inv, hyx,
        inv_mul_cancel]
    have hx' : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥L) : G) := by simp
    rw [hx']
    have hker' : y⁻¹ * ⟨x, hx⟩ ∈ CFSG.Open.pCore 2 ↥L := by
      exact hker
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hy) ⟨y⁻¹ * ⟨x, hx⟩, hker', rfl⟩
  · right
    rw [Subgroup.commutator_le]
    intro n hn l hl
    have hnL := hNL hn
    have hc : f ⟨n, hnL⟩ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
      h ⟨⟨n, hnL⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
    have h1 : f ⁅(⟨n, hnL⟩ : ↥L), ⟨l, hl⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hc (f ⟨l, hl⟩)).symm
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
    have h1' : ⁅(⟨n, hnL⟩ : ↥L), ⟨l, hl⟩⁆ ∈ CFSG.Open.pCore 2 ↥L := by
      exact h1
    exact ⟨⁅(⟨n, hnL⟩ : ↥L), ⟨l, hl⟩⁆, h1', rfl⟩

omit [Finite G] in
theorem conjAct_eq_one_iff_82 {V : Subgroup G} (g : Subgroup.normalizer (V : Set G)) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h3 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h
    simp only [CFSG.QuasithinUnique.Setup.coe_conjAct_apply, MulAut.one_apply] at h3
    calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * g := by rw [h3]
      _ = g * v := by group
  · intro h
    ext v
    simp only [CFSG.QuasithinUnique.Setup.coe_conjAct_apply, MulAut.one_apply]
    rw [← Subgroup.mem_centralizer_iff.mp h v v.2]
    group

theorem commutator_L_eq_of_82 (hsimp : HSimple82) (hcent : HCent82) (hyp : Hyp7_0_2 G T L I)
    {V A : Subgroup G} [hc : IsMulCommutative ↥V] (hmod : IsModel82 (V := ↥V) (autOn L V))
    (hLN : L ≤ Subgroup.normalizer (V : Set G)) (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hAC : ¬ A ≤ Subgroup.centralizer (V : Set G))
    (hQC : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) : ⁅L, A⁆ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, a₀, b₀, hab⟩ := hsimp ↥V (autOn L V) hmod
  have hNL : ⁅L, A⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro l hl a ha
    rw [commutatorElement_def]
    have h1 : a * l⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAL ha) l⁻¹).mp (L.inv_mem hl)
    have := L.mul_mem hl h1
    simpa [mul_assoc] using this
  have hLN' : L ≤ Subgroup.normalizer ((⁅L, A⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left L A
  rcases sup_pCoreOf_eq_or_commutator_le_of_82 hyp.fsu.quasisimple hNL hLN' with h | h
  ·
    refine hyp.fsu.faithful.2.1 _ hNL (Subgroup.normal_subgroupOf_of_le_normalizer hLN') ?_
    intro x hx
    rw [← h] at hx
    obtain ⟨n, hn, q, hq, rfl⟩ := mem_sup_of_le_normalizer_82
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLN') hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨q, hq⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hpow : ∀ m : ℕ, ∃ n' ∈ ⁅L, A⁆, (n * q) ^ m = n' * q ^ m := by
      intro m
      induction m with
      | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
      | succ m ih =>
        obtain ⟨n', hn', he⟩ := ih
        have hqL : q ^ m ∈ L := L.pow_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 L hq) m
        have h1 : q ^ m * n * (q ^ m)⁻¹ ∈ ⁅L, A⁆ :=
          (Subgroup.mem_normalizer_iff.mp (hLN' hqL) n).mp hn
        refine ⟨n' * (q ^ m * n * (q ^ m)⁻¹), Subgroup.mul_mem _ hn' h1, ?_⟩
        rw [pow_succ, he, pow_succ]
        group
    obtain ⟨n', hn', he⟩ := hpow (2 ^ k)
    rw [he, hk', mul_one]
    exact hn'
  ·
    exfalso
    have hZ : Subgroup.center ↥(autOn L V) = ⊥ := by
      rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(autOn L V)) with hc0 | hc0
      · exact hc0
      · exact absurd (Subgroup.mem_center_iff.mp (hc0 ▸ Subgroup.mem_top b₀) a₀) hab
    have hNC : ⁅L, A⁆ ≤ Subgroup.centralizer (V : Set G) := by
      intro y hy
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := hLN (hNL hy)
      have hyH : conjAct V ⟨y, hyN⟩ ∈ autOn L V := ⟨⟨y, hyN⟩, hNL hy, rfl⟩
      have hcen : (⟨conjAct V ⟨y, hyN⟩, hyH⟩ : ↥(autOn L V)) ∈ Subgroup.center ↥(autOn L V) := by
        rw [Subgroup.mem_center_iff]
        rintro ⟨_, ⟨l, hl, rfl⟩⟩
        apply Subtype.ext
        have hlL : (l : G) ∈ L := hl
        have h1 : ⁅y, (l : G)⁆ ∈ pCoreOf 2 L :=
          h (Subgroup.commutator_mem_commutator hy hlL)
        have h2 := (conjAct_eq_one_iff_82 (V := V) (⟨y, hyN⟩ * l * ⟨y, hyN⟩⁻¹ * l⁻¹)).mpr
          (by simpa [commutatorElement_def] using hQC h1)
        simp only [map_mul, map_inv] at h2
        change conjAct V l * conjAct V ⟨y, hyN⟩ = conjAct V ⟨y, hyN⟩ * conjAct V l
        have h3 := congrArg (· * (conjAct V l * conjAct V ⟨y, hyN⟩)) h2
        simp only [one_mul] at h3
        rw [← h3]
        group
      rw [hZ, Subgroup.mem_bot] at hcen
      exact (conjAct_eq_one_iff_82 ⟨y, hyN⟩).mp (congrArg Subtype.val hcen)
    apply hAC
    intro a ha
    have haN : a ∈ Subgroup.normalizer (V : Set G) := hAN ha
    have hcentr : conjAct V ⟨a, haN⟩ ∈ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨l, hl, rfl⟩
      have hlL : (l : G) ∈ L := hl
      have h1 : ⁅(l : G), a⁆ ∈ ⁅L, A⁆ := Subgroup.commutator_mem_commutator hlL ha
      have h2 := (conjAct_eq_one_iff_82 (V := V) (l * ⟨a, haN⟩ * l⁻¹ * ⟨a, haN⟩⁻¹)).mpr
        (by simpa [commutatorElement_def] using hNC h1)
      simp only [map_mul, map_inv] at h2
      have h3 := congrArg (· * (conjAct V ⟨a, haN⟩ * conjAct V l)) h2
      simp only [one_mul] at h3
      rw [← h3]
      group
    rw [hcent ↥V (autOn L V) hmod, Subgroup.mem_bot] at hcentr
    exact (conjAct_eq_one_iff_82 ⟨a, haN⟩).mp hcentr

omit [Finite G] in
theorem commutator_Q_L_le_of_82 {V A Q : Subgroup G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hQA : ⁅Q, A⁆ ≤ V) (hLA : ⁅L, A⁆ = L) : ⁅Q, L⁆ ≤ V := by
  let S : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (Q : Set G) ∧
        g ∈ Subgroup.normalizer (V : Set G) ∧ ∀ q ∈ Q, ⁅q, g⁆ ∈ V}
      one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun q _ => by
        rw [commutatorElement_one_right]
        exact V.one_mem⟩
      mul_mem' := by
        rintro g h ⟨hgQ, hgV, hg⟩ ⟨hhQ, hhV, hh⟩
        refine ⟨Subgroup.mul_mem _ hgQ hhQ, Subgroup.mul_mem _ hgV hhV, fun q hq => ?_⟩
        have h1 : ⁅q, g * h⁆ = ⁅q, g⁆ * (g * ⁅q, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact V.mul_mem (hg q hq) ((Subgroup.mem_normalizer_iff.mp hgV _).mp (hh q hq))
      inv_mem' := by
        rintro g ⟨hgQ, hgV, hg⟩
        refine ⟨Subgroup.inv_mem _ hgQ, Subgroup.inv_mem _ hgV, fun q hq => ?_⟩
        have h1 : ⁅q, g⁻¹⁆ = g⁻¹ * ⁅q, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV) _).mp
          (V.inv_mem (hg q hq)) }
  have hAS : A ≤ S := fun a ha =>
    ⟨hAQ ha, hAV ha, fun q hq => hQA (Subgroup.commutator_mem_commutator hq ha)⟩
  have hconj : ∀ l ∈ L, ∀ x ∈ S, l * x * l⁻¹ ∈ S := by
    rintro l hl x ⟨hxQ, hxV, hx⟩
    have hlQ := hLQ hl
    have hlV := hLV hl
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hlQ hxQ) (Subgroup.inv_mem _ hlQ),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hlV hxV) (Subgroup.inv_mem _ hlV), fun q hq => ?_⟩
    have hq' : l⁻¹ * q * l⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlQ) q).mp hq
    have h1 : ⁅q, l * x * l⁻¹⁆ = l * ⁅l⁻¹ * q * l⁻¹⁻¹, x⁆ * l⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp hlV _).mp (hx _ hq')
  have hLS : L ≤ S := by
    rw [← hLA, Subgroup.commutator_le]
    intro l hl a ha
    rw [commutatorElement_def]
    exact S.mul_mem (hconj l hl a (hAS ha)) (S.inv_mem (hAS ha))
  rw [Subgroup.commutator_le]
  intro q hq l hl
  exact (hLS hl).2.2 q hq

theorem inf_centralizer_le_pCoreOf_of_82 (hF : quasithinGenFitting L = pCoreOf 2 L)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hQL : ⁅pCoreOf 2 L, L⁆ ≤ V) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hodd : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ m : ℕ, Odd m → x ^ m = 1 →
      x = 1 := by
    rintro x ⟨hxL, hxC⟩ m hm hxm
    have hcomm : ∀ q ∈ pCoreOf 2 L, x * q * x⁻¹ = q := by
      intro q hq
      set w := x * q * x⁻¹ * q⁻¹ with hw
      have hwV : w ∈ V := by
        have h1 : ⁅q, x⁆ ∈ V := hQL (Subgroup.commutator_mem_commutator hq hxL)
        have h2 : w = ⁅q, x⁆⁻¹ := by
          rw [hw, commutatorElement_def]
          group
        rw [h2]
        exact V.inv_mem h1
      have hxw : x * w * x⁻¹ = w := by
        rw [← Subgroup.mem_centralizer_iff.mp hxC w hwV]
        group
      have hpow : ∀ n : ℕ, x ^ n * q * (x ^ n)⁻¹ = w ^ n * q := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have h1 : x ^ (n + 1) * q * (x ^ (n + 1))⁻¹ = x * (x ^ n * q * (x ^ n)⁻¹) * x⁻¹ := by
            group
          have hxwn : x * w ^ n * x⁻¹ = w ^ n := by
            rw [← conj_pow, hxw]
          rw [h1, ih, pow_succ]
          calc x * (w ^ n * q) * x⁻¹ = (x * w ^ n * x⁻¹) * (x * q * x⁻¹) := by group
            _ = w ^ n * (w * q) := by rw [hxwn, show x * q * x⁻¹ = w * q by rw [hw]; group]
            _ = w ^ n * w * q := by group
      have h1 := hpow m
      rw [hxm, one_mul, inv_one, mul_one] at h1
      have hwm : w ^ m = 1 := by
        have := congrArg (· * q⁻¹) h1
        simpa using this.symm
      have hw2 : w ^ 2 = 1 := hV.2 w hwV
      have hw1 : w = 1 := by
        have h3 : w ^ Nat.gcd m 2 = 1 := pow_gcd_eq_one.mpr ⟨hwm, hw2⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_right).mpr hm), pow_one] at h3
      have h4 : x * q * x⁻¹ * q⁻¹ = 1 := hw1
      calc x * q * x⁻¹ = x * q * x⁻¹ * q⁻¹ * q := by group
        _ = q := by rw [h4, one_mul]
    have hxQ : x ∈ pCoreOf 2 L := by
      rw [← hF]
      refine centralizer_quasithinGenFitting_le L ⟨hxL, ?_⟩
      rw [hF]
      refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
      calc q * x = x * q * x⁻¹ * x := by rw [hcomm q hq]
        _ = x * q := by group
    obtain ⟨k, hk⟩ := hQp ⟨x, hxQ⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : x ^ Nat.gcd m (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hxm, hk'⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k ((Nat.coprime_two_right).mpr hm)),
      pow_one] at h3
  have hCp : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    intro c
    obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine ⟨a, ?_⟩
    have h1 : (c ^ 2 ^ a : ↥(L ⊓ Subgroup.centralizer (V : Set G))) ^ m = 1 := by
      rw [← pow_mul, ← he, pow_orderOf_eq_one]
    have h2 := hodd ((c ^ 2 ^ a : ↥(L ⊓ Subgroup.centralizer (V : Set G))) : G)
      (c ^ 2 ^ a).2 m hm (by simpa using congrArg Subtype.val h1)
    exact Subtype.ext (by simpa using h2)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hCp
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hlV := hLN hl
  constructor
  · rintro ⟨hxL, hxC⟩
    refine ⟨L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    have hv' : l⁻¹ * v * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlV) v).mp hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hxC _ hv'
    calc v * (l * x * l⁻¹) = l * ((l⁻¹ * v * l) * x) * l⁻¹ := by group
      _ = l * (x * (l⁻¹ * v * l)) * l⁻¹ := by rw [h1]
      _ = l * x * l⁻¹ * v := by group
  · rintro ⟨hxL, hxC⟩
    have hx' : x = l⁻¹ * (l * x * l⁻¹) * l := by group
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · rw [hx']
      exact L.mul_mem (L.mul_mem (L.inv_mem hl) hxL) hl
    · intro v hv
      have hv' : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hlV v).mp hv
      have h1 := Subgroup.mem_centralizer_iff.mp hxC _ hv'
      calc v * x = l⁻¹ * ((l * v * l⁻¹) * (l * x * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * x * l⁻¹) * (l * v * l⁻¹)) * l := by rw [h1]
        _ = x * v := by group

end L8210B

end CFSG.Quasithin.H13
