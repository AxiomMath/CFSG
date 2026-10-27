module

public import CFSG.Quasithin.H13.U3L14Set
public import CFSG.Quasithin.H13.U3L14Grp
public import CFSG.Quasithin.H13.U3L14Rank
public import CFSG.Quasithin.EmptyFaithful.S146D2
public import CFSG.Quasithin.H13.U3FrameKernel
public import CFSG.Quasithin.H13.A6S4L0
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.U3L15Gen

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ centralizer (A : Set G))
    (hB : x ∈ centralizer (B : Set G)) : x ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h : A ⊔ B ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hA a ha
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hB b hb
  rw [mem_centralizer_iff]
  intro y hy
  exact mem_centralizer_singleton_iff.1 (h hy)

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

omit [Finite G] S in
theorem Y_CV3 : oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≤
    centralizer (V₃ : Set G) :=
  (oTwoUpper_le _).trans (centralizer_le V3_U)

theorem Y_CV2 : oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≤
    centralizer (V₂ : Set G) :=
  Y_CV3.trans (centralizer_le S.le23)

theorem CV2_G1 : centralizer (V₂ : Set G) ≤ A6.g1 T V :=
  (centralizer_le S.le12).trans (centralizer_le_normalizer _)

theorem Y_G1 : oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≤ A6.g1 T V :=
  S.Y_CV2.trans S.CV2_G1

omit [Finite G] S in
theorem G1_NY : A6.g1 T V ≤
    normalizer (oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) : Set G) :=
  fun _ hg => normalizer_le_normalizer_oTwoUpper _
    (mem_normalizer_centralizer (le_normalizer_conjClosure V₃ (A6.g1 T V) hg))

theorem YM_NV : oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ⊓
    normalizer (L : Set G) ≤ normalizer (V : Set G) := by
  rw [S.ti _ _ S.V1_ne le1V S.Y_G1]
  exact inf_le_right

theorem Y0_CV {Y₀ : Subgroup G} (hN : Y₀ ≤ normalizer (V : Set G))
    (h3 : Y₀ ≤ centralizer (V₃ : Set G)) (h2 : Y₀ = oTwoUpper Y₀) :
    Y₀ ≤ centralizer (V : Set G) := by
  refine h2.le.trans ?_
  rw [oTwoUpper, closure_le]
  rintro y ⟨hy, ho⟩
  exact S.cv3 y ⟨hN hy, h3 hy⟩ ho

theorem O2L_T : pCoreOf 2 L ≤ T :=
  (pCoreOf_le_pCoreOf_sup S.T_L).trans (pCoreOf_two_le_of_isSylowTwoOf (S.syl le_sup_right))

theorem L_NY0 {Y₀ : Subgroup G} (hN : Y₀ ≤ normalizer (V : Set G) ⊓ normalizer (L : Set G))
    (h3 : Y₀ ≤ centralizer (V₃ : Set G)) (h2 : Y₀ = oTwoUpper Y₀)
    (hT : T ≤ normalizer (Y₀ : Set G)) : L ≤ normalizer (Y₀ : Set G) := by
  have hCV := S.Y0_CV (fun y hy => (hN hy).1) h3 h2
  have hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := S.fsu.quasisimple.1
  have hcomm : ∀ y ∈ Y₀, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro y hy
    refine comm_mem_pCoreOf_of_central hperf (hN hy).2 fun l hl m hm => ?_
    have hc : y * l * y⁻¹ * l⁻¹ ∈ L ⊓ centralizer (V : Set G) := by
      refine mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 (hN hy).2 l).1 hl) (inv_mem hl), ?_⟩
      rw [mem_centralizer_iff]
      intro v hv
      have hv' : l⁻¹ * v * l ∈ V := by
        have := (mem_normalizer_iff.1 (S.L_NV (inv_mem hl)) v).1 hv
        simpa using this
      have hyv : ∀ u ∈ V, u * y = y * u := fun u hu => (mem_centralizer_iff.1 (hCV hy)) u hu
      have hyv' : (l⁻¹ * v * l) * y⁻¹ = y⁻¹ * (l⁻¹ * v * l) := by
        have := hyv _ hv'
        calc (l⁻¹ * v * l) * y⁻¹ = y⁻¹ * (y * (l⁻¹ * v * l)) * y⁻¹ := by group
          _ = y⁻¹ * ((l⁻¹ * v * l) * y) * y⁻¹ := by rw [this]
          _ = y⁻¹ * (l⁻¹ * v * l) := by group
      calc v * (y * l * y⁻¹ * l⁻¹) = (v * y) * l * y⁻¹ * l⁻¹ := by group
        _ = (y * v) * l * y⁻¹ * l⁻¹ := by rw [hyv v hv]
        _ = y * l * ((l⁻¹ * v * l) * y⁻¹) * l⁻¹ := by group
        _ = y * l * (y⁻¹ * (l⁻¹ * v * l)) * l⁻¹ := by rw [hyv']
        _ = y * l * y⁻¹ * l⁻¹ * v := by group
    obtain ⟨-, hc'⟩ := A6.mem_o2Z_iff.1 (S.clv hc)
    exact hc' m hm
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hOY : pCoreOf 2 L ≤ normalizer (Y₀ : Set G) := S.O2L_T.trans hT
  have hW : oTwoUpper (Y₀ ⊔ pCoreOf 2 L) = Y₀ := oTwoUpper_sup_eq h2 hO2 hOY
  intro l hl
  have hlW : l ∈ normalizer ((Y₀ ⊔ pCoreOf 2 L : Subgroup G) : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
    have hle : Y₀ ⊔ pCoreOf 2 L ≤ (Y₀ ⊔ pCoreOf 2 L).comap (MulAut.conj l).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun o ho => ?_)
      · show l * y * l⁻¹ ∈ Y₀ ⊔ pCoreOf 2 L
        have h1 := hcomm y hy l hl
        have h1' : l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
          have := inv_mem h1
          rwa [show (y * l * y⁻¹ * l⁻¹)⁻¹ = l * y * l⁻¹ * y⁻¹ by group] at this
        rw [show l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y by group]
        exact mul_mem (mem_sup_right h1') (mem_sup_left hy)
      · show l * o * l⁻¹ ∈ Y₀ ⊔ pCoreOf 2 L
        exact mem_sup_right ((mem_normalizer_iff.1
          (LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) o).1 ho)
    exact hle hx
  rw [← hW]
  exact normalizer_le_normalizer_oTwoUpper _ hlW

theorem NY0_M {Y₀ : Subgroup G} (hN : Y₀ ≤ normalizer (V : Set G) ⊓ normalizer (L : Set G))
    (h3 : Y₀ ≤ centralizer (V₃ : Set G)) (h2 : Y₀ = oTwoUpper Y₀)
    (hT : T ≤ normalizer (Y₀ : Set G)) (hG1 : Y₀ ≤ A6.g1 T V) (h1 : Y₀ ≠ ⊥) :
    normalizer (Y₀ : Set G) ≤ normalizer (L : Set G) := by
  have hL := S.L_NY0 hN h3 h2 hT
  have hc1 : CharTwo (Y₀ ⊔ T) := charTwo_of_pCore_centralizer_le S.charTwo_G1
    (sup_le hG1 S.T_G1) (inf_le_left.trans (S.Q1_T.trans le_sup_right))
  have hc2 : CharTwo Y₀ :=
    hc1.of_normal le_sup_left (normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hT))
  have hO : pCoreOf 2 Y₀ ≠ ⊥ := by
    intro hb
    apply h1
    rw [eq_bot_iff]
    intro y hy
    have hyc : y ∈ centralizer (pCoreOf 2 Y₀ : Set G) := by
      rw [hb, mem_centralizer_iff]
      intro h hh
      rw [show h = 1 from hh]
      group
    have := hc2 ⟨hy, hyc⟩
    rw [hb] at this
    exact this
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 Y₀ : Set G)) :=
    ⟨_, hO, LieType.BorelTits.pCoreOf_isPGroup 2 Y₀, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hNN := LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hM'L := S.uniq M' hM' ((sup_le hL hT).trans (hNN.trans hle))
  exact hNN.trans (hM'L ▸ hle)

theorem Y_not_M (h1336 : A6.Stmt13_3_6)
    (hY : oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≠ ⊥) :
    ¬ oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≤ normalizer (L : Set G) := by
  intro hYM
  have hN : oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≤
      normalizer (V : Set G) ⊓ normalizer (L : Set G) := fun y hy =>
    ⟨S.YM_NV ⟨hy, hYM hy⟩, hYM hy⟩
  have h2 := (oTwoUpper_oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))).symm
  have hNY := S.NY0_M hN Y_CV3 h2 (S.T_G1.trans G1_NY) S.Y_G1 hY
  have hG1 : A6.g1 T V ≤ normalizer (L : Set G) := G1_NY.trans hNY
  rcases h1336 G T L V S.h13 S.irr with h | ⟨h, -⟩
  · exact h hG1
  · exact h S.zv

omit [Finite G] S in
theorem conj_CV2 {g : G} (hg : g ∈ normalizer (V₂ : Set G)) {c : G}
    (hc : c ∈ centralizer (V₂ : Set G)) : g * c * g⁻¹ ∈ centralizer (V₂ : Set G) :=
  (mem_normalizer_iff.1 (mem_normalizer_centralizer hg) c).1 hc

theorem Y_NYg {g : G} (hg : g ∈ normalizer (V₂ : Set G)) :
    oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≤
      normalizer ((oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))).map
        (MulAut.conj g).toMonoidHom : Set G) := by
  set Y := oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) with hYdef
  intro y hy
  refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
  rw [mem_map_conj_iff] at hx ⊢
  have hy' : g⁻¹ * y * g ∈ A6.g1 T V := by
    have := conj_CV2 (inv_mem hg) (S.Y_CV2 hy)
    exact S.CV2_G1 (by simpa using this)
  have := (mem_normalizer_iff.1 (G1_NY hy') _).1 hx
  rw [show g⁻¹ * (y * x * y⁻¹) * g = (g⁻¹ * y * g) * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹ by group]
  exact this

theorem Yg_NY {g : G} (hg : g ∈ normalizer (V₂ : Set G)) :
    (oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))).map
      (MulAut.conj g).toMonoidHom ≤
      normalizer (oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) : Set G) := by
  intro x hx
  rw [mem_map_conj_iff] at hx
  have h1 : x ∈ centralizer (V₂ : Set G) := by
    have := conj_CV2 hg (S.Y_CV2 hx)
    simpa [mul_assoc] using this
  exact G1_NY (S.CV2_G1 h1)

theorem Yg_CV2 {g : G} (hg : g ∈ normalizer (V₂ : Set G)) :
    (oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))).map
      (MulAut.conj g).toMonoidHom ≤ centralizer (V₂ : Set G) := by
  intro x hx
  rw [mem_map_conj_iff] at hx
  have := conj_CV2 hg (S.Y_CV2 hx)
  simpa [mul_assoc] using this

theorem isPGroup_Y_inter (h1336 : A6.Stmt13_3_6) {g : G} (hgL : g ∈ L)
    (hg2 : g ∈ normalizer (V₂ : Set G))
    (hgM : centralizer ((V₃ ⊔ V₃.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    IsPGroup 2 ↥(oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ⊓
      (oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))).map
        (MulAut.conj g).toMonoidHom) := by
  set Y := oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) with hYdef
  set Yg := Y.map (MulAut.conj g).toMonoidHom with hYgdef
  set M := normalizer (L : Set G) with hM
  have hYg3 : Yg ≤ centralizer ((V₃.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_map_conj_iff] at hx
    rw [mem_centralizer_iff]
    intro w hw
    replace hw := mem_map_conj_iff.1 hw
    have h1 := (mem_centralizer_iff.1 (Y_CV3 hx)) _ hw
    calc w * x = g * ((g⁻¹ * w * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = x * w := by group
  have hinter : Y ⊓ Yg ≤ M := fun x hx =>
    hgM (mem_centralizer_sup (Y_CV3 hx.1) (hYg3 hx.2))
  set YM := oTwoUpper (Y ⊓ M) with hYM
  have hYMY : YM ≤ Y := (oTwoUpper_le _).trans inf_le_left
  have hYMM : YM ≤ M := (oTwoUpper_le _).trans inf_le_right
  have hYMN : YM ≤ normalizer (V : Set G) ⊓ M := fun y hy =>
    ⟨S.YM_NV ⟨hYMY hy, hYMM hy⟩, hYMM hy⟩
  have hYM2 : YM = oTwoUpper YM := (oTwoUpper_oTwoUpper _).symm
  have hTYM : T ≤ normalizer (YM : Set G) := fun t ht =>
    normalizer_le_normalizer_oTwoUpper _
      (mem_normalizer_inf (G1_NY (S.T_G1 ht)) (le_normalizer (S.T_L ht)))
  have hLYM := S.L_NY0 hYMN (hYMY.trans Y_CV3) hYM2 hTYM
  set Y₁ := oTwoUpper (Y ⊓ Yg) with hY₁
  have hYMYg : YM ≤ Yg := by
    intro x hx
    rw [mem_map_conj_iff]
    have h1 := (mem_normalizer_iff.1 (hLYM (inv_mem hgL)) x).1 hx
    have h2 : g⁻¹ * x * g ∈ YM := by simpa using h1
    exact hYMY h2
  have h1 : YM ≤ Y₁ := hYM2.le.trans (oTwoUpper_mono (le_inf hYMY hYMYg))
  have h2 : Y₁ ≤ YM := oTwoUpper_mono (le_inf inf_le_left hinter)
  have hY₁eq : Y₁ = YM := le_antisymm h2 h1
  by_cases hY : Y = ⊥
  · rw [hY, bot_inf_eq]
    exact IsPGroup.of_bot
  have hY₁ : Y₁ = ⊥ := by
    by_contra hne
    have hYMne : YM ≠ ⊥ := hY₁eq ▸ hne
    have hNM := S.NY0_M hYMN (hYMY.trans Y_CV3) hYM2 hTYM (hYMY.trans S.Y_G1) hYMne
    have hYN : Y ≤ normalizer (Y₁ : Set G) := fun y hy =>
      normalizer_le_normalizer_oTwoUpper _ (mem_normalizer_inf (le_normalizer hy) (S.Y_NYg hg2 hy))
    exact S.Y_not_M h1336 hY (hYN.trans (hY₁eq ▸ hNM))
  exact isPGroup_of_oTwoUpper_eq_bot hY₁

theorem card_le_of_inter {g : G} (hg2 : g ∈ normalizer (V₂ : Set G))
    (h2 : IsPGroup 2 ↥(oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ⊓
      (oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))).map
        (MulAut.conj g).toMonoidHom))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hEY : E ≤ oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  set Y := oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) with hYdef
  set Yg := Y.map (MulAut.conj g).toMonoidHom with hYgdef
  set N := Y ⊓ Yg with hNdef
  set F := E.map (MulAut.conj g).toMonoidHom with hFdef
  have hFYg : F ≤ Yg := map_mono hEY
  have hFcard : Nat.card F = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hF : IsElemAbelian p F := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha, h1⟩ := mem_map.1 x.2
      obtain ⟨b, hb, h2⟩ := mem_map.1 y.2
      show (x : G) * y = y * x
      rw [← h1, ← h2, ← map_mul, ← map_mul]
      congr 1
      have := hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩
      simpa using congrArg Subtype.val this
    · obtain ⟨a, ha, rfl⟩ := mem_map.1 hx
      rw [← map_pow, hE.2 a ha, map_one]
  have hYNYg := S.Y_NYg hg2
  have hYgNY := S.Yg_NY hg2
  have hEN : E ≤ normalizer (N : Set G) := fun e he =>
    mem_normalizer_inf (le_normalizer (hEY he)) (hYNYg (hEY he))
  have hFN : F ≤ normalizer (N : Set G) := fun f hf =>
    mem_normalizer_inf (hYgNY (hFYg hf)) (le_normalizer (hFYg hf))
  have hEF : ∀ e ∈ E, ∀ f ∈ F, e * f * e⁻¹ * f⁻¹ ∈ N := by
    intro e he f hf
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [show e * f * e⁻¹ * f⁻¹ = e * (f * e⁻¹ * f⁻¹) by group]
      exact mul_mem (hEY he) ((mem_normalizer_iff.1 (hYgNY (hFYg hf)) e⁻¹).1
        (inv_mem (hEY he)))
    · exact mul_mem ((mem_normalizer_iff.1 (hYNYg (hEY he)) f).1 (hFYg hf)) (inv_mem (hFYg hf))
  have hEp : ∀ e ∈ E, e ∈ N → e = 1 := by
    intro e he heN
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem h2 heN
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hE.2 e he))
      (orderOf_dvd_of_pow_eq_one hk)
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hint : ∀ e ∈ E, ∀ f ∈ F, ∀ n ∈ N, e = f * n → e = 1 := by
    intro e he f hf n hn hefn
    refine hEp e he ⟨hEY he, ?_⟩
    rw [hefn]
    exact mul_mem (hFYg hf) hn.2
  obtain ⟨P, hPle, hPA, hPcard⟩ :=
    exists_elemAbelian_of_commute_mod hp2 h2 hEN hFN hE hF hEF hint
  have hPG2 : P ≤ normalizer (V₂ : Set G) := by
    refine hPle.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact (hEY.trans S.Y_CV2).trans (centralizer_le_normalizer _)
    · exact (hFYg.trans (S.Yg_CV2 hg2)).trans (centralizer_le_normalizer _)
    · exact (inf_le_left.trans S.Y_CV2).trans (centralizer_le_normalizer _)
  have hV2ne : V₂ ≠ ⊥ := fun h => S.V1_ne (le_bot_iff.1 (h ▸ S.le12))
  have hV2p : IsPGroup 2 V₂ := S.isP_T.to_le (S.le2V.trans S.V_T)
  have hloc : IsTwoLocal (normalizer (V₂ : Set G)) := ⟨V₂, hV2ne, hV2p, rfl⟩
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hPA.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hPp.exists_card_eq
  have hk2 : k ≤ 2 := by
    have h1 := CFSG.SectionRank.le_pRank hp.one_lt hPG2 hPA hk
    have hev := A1b.pRank_le_evenRank hp hp2 hloc
    have hq : CFSG.Open.evenRank G ≤ 2 := S.h13.qtke.2.2
    omega
  have hEp' : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨j, hj⟩ := hEp'.exists_card_eq
  rw [hFcard, hj, hk, ← pow_add] at hPcard
  have hjk : j + j ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 hPcard
  rw [hj]
  calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    _ = p := pow_one p

theorem stepB (h1336 : A6.Stmt13_3_6) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) :
    Group.IsSolvable ↥(oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G,
        E ≤ oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) →
          IsElemAbelian p E → Nat.card E ≤ p := by
  set Y := oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) with hYdef
  have hbot : Y = ⊥ → Group.IsSolvable ↥Y ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G,
      E ≤ Y → IsElemAbelian p E → Nat.card E ≤ p := by
    intro h
    refine ⟨?_, fun p hp _ E hE _ => ?_⟩
    · rw [isSolvable_iff_perfectCore_eq_bot, eq_bot_iff, h]
      exact perfectCore_le _
    · rw [h, le_bot_iff] at hE
      rw [hE, card_bot]
      exact hp.one_lt.le
  rcases S.bcase with hC | ⟨g, ⟨hgL, hg2⟩, hg3, hg1, hgM⟩
  · refine hbot ?_
    by_contra hY
    exact S.Y_not_M h1336 hY (Y_CV3.trans hC)
  by_cases hY : Y = ⊥
  · exact hbot hY
  have h2 := S.isPGroup_Y_inter h1336 hgL hg2 hgM
  refine ⟨?_, fun p hp hp2 E hEY hE => S.card_le_of_inter hg2 h2 hp hp2 hEY hE⟩
  by_contra hns
  have hK := S.h13.qtke
  have hs := S.h13.simple
  have hnab := S.h13.nonabelian
  have hYc : CharTwo Y := S.charTwo_G1.of_normal S.Y_G1 (normal_subgroupOf_of_le_normalizer G1_NY)
  have hO2Y : pCoreOf 2 Y ≠ ⊥ := by
    intro hb
    apply hY
    rw [eq_bot_iff]
    intro y hy
    have hyc : y ∈ centralizer (pCoreOf 2 Y : Set G) := by
      rw [hb, mem_centralizer_iff]
      intro h hh
      rw [show h = 1 from hh]
      group
    have := hYc ⟨hy, hyc⟩
    rw [hb] at this
    exact this
  have hspan := lemma_1_2_1_one hK hs hnab h39 hO2Y
  have hpc : perfectCore Y ≠ ⊥ := fun h => hns ((isSolvable_iff_perfectCore_eq_bot Y).2 h)
  obtain ⟨K, hKY⟩ : ∃ K, K ∈ cComp Y := by
    by_contra hnone
    push Not at hnone
    apply hpc
    rw [← hspan, cCompSpan, eq_bot_iff]
    exact sSup_le fun K hK => absurd hK (hnone K)
  have hYsub : CFSG.Open.IsSubnormal Y (normalizer (V₂ : Set G)) := by
    refine CFSG.Open.IsSubnormal.step S.Y_CV2 ?_
      (CFSG.Open.IsSubnormal.step (centralizer_le_normalizer _) ?_ (CFSG.Open.IsSubnormal.refl _))
    · exact normal_subgroupOf_of_le_normalizer (fun c hc => G1_NY (S.CV2_G1 hc))
    · exact normal_subgroupOf_of_le_normalizer (fun n hn => mem_normalizer_centralizer hn)
  have hKG2 := cComp_mem_of_subnormal hYsub hKY
  have hV2ne : V₂ ≠ ⊥ := fun h => S.V1_ne (le_bot_iff.1 (h ▸ S.le12))
  have hO2G2 : pCoreOf 2 (normalizer (V₂ : Set G)) ≠ ⊥ := by
    intro hb
    apply hV2ne
    have hV2p : IsPGroup 2 V₂ := S.isP_T.to_le (S.le2V.trans S.V_T)
    have := CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer le_normalizer le_rfl hV2p
    rw [hb] at this
    exact le_bot_iff.1 this
  have hgo : Odd (orderOf g) := by
    have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h <;> rw [h] <;> decide
  have hgK := odd_mem_normalizer_of_mem_cComp hK hs hnab h37 h38 hO2G2 hKG2 hg2 hgo
  have hKle : K ≤ Y ⊓ Y.map (MulAut.conj g).toMonoidHom := by
    intro k hk
    refine Subgroup.mem_inf.2 ⟨le_of_mem_cComp hKY hk, mem_map_conj_iff.2 ?_⟩
    have h1 := (mem_normalizer_iff.1 (inv_mem hgK) k).1 hk
    have h2 : g⁻¹ * k * g ∈ K := by simpa using h1
    exact le_of_mem_cComp hKY h2
  exact not_isPGroup_of_perfect (perfect_of_mem_cComp hKY) (ne_bot_of_mem_cComp hKY)
    (h2.to_le hKle)

end Set14

end CFSG.Quasithin.H13.U3
