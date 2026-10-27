module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LG4App
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LPsl2
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE5cG

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

theorem dih_relations {Kb : Type} [Group Kb] (A : Subgroup Kb) (xb ab sb : Kb)
    (hA : ∀ w ∈ A, w = 1 ∨ w = ab) (hab1 : ab ≠ 1) (hab2 : ab * ab = 1) (haA : ab ∈ A)
    (hx3 : orderOf xb = 3) (hxa : ab * xb = xb * ab)
    (hsA : sb ∈ Subgroup.normalizer (A : Set Kb)) (hsxA : sb * xb * sb⁻¹ * xb ∈ A) :
    sb * ab = ab * sb ∧ sb * xb * sb⁻¹ = xb⁻¹ ∧ sb ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab : orderOf ab = 2 := orderOf_eq_prime (by rw [pow_two]; exact hab2) hab1
  have hsx : sb * xb * sb⁻¹ = xb⁻¹ := by
    rcases hA _ hsxA with h | h
    · exact mul_eq_one_iff_eq_inv.mp h
    · exfalso
      have h1 : sb * xb * sb⁻¹ = ab * xb⁻¹ := eq_mul_inv_of_mul_eq h
      have h3 : orderOf (sb * xb * sb⁻¹) = 3 := by
        have := orderOf_injective (MulAut.conj sb).toMonoidHom (MulAut.conj sb).injective xb
        simpa [MulAut.conj_apply, hx3] using this
      have hc : Commute ab xb⁻¹ := (show Commute ab xb from hxa).inv_right
      have h6 : orderOf (ab * xb⁻¹) = 6 := by
        rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hab, orderOf_inv, hx3]; norm_num),
          hab, orderOf_inv, hx3]
      rw [h1, h6] at h3
      omega
  refine ⟨?_, hsx, ?_⟩
  · have h1 : sb * ab * sb⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hsA ab).mp haA
    rcases hA _ h1 with h | h
    · exfalso
      apply hab1
      have : ab = sb⁻¹ * (sb * ab * sb⁻¹) * sb := by group
      rw [this, h]
      group
    · exact mul_inv_eq_iff_eq_mul.mp h
  · intro hs1
    rw [hs1] at hsx
    simp only [inv_one, one_mul, mul_one] at hsx
    have hx2 : xb ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr hsx
    have := orderOf_dvd_of_pow_eq_one hx2
    rw [hx3] at this
    omega

theorem mem_normalizer_of_key {G : Type} [Group G] [Finite G] {K R : Subgroup G} {w : G}
    (hOR : pCoreOf 2 K ≤ R) (key : ∀ r ∈ R, r * w * r⁻¹ * w⁻¹ ∈ pCoreOf 2 K) :
    w ∈ Subgroup.normalizer (R : Set G) := by
  have hw1 : ∀ r ∈ R, w * r * w⁻¹ ∈ R := by
    intro r hr
    have h1 := key r⁻¹ (R.inv_mem hr)
    have h3 : r⁻¹ * w * r * w⁻¹ ∈ R := by simpa using hOR h1
    rw [show w * r * w⁻¹ = r * (r⁻¹ * (w * r * w⁻¹)) by group]
    refine R.mul_mem hr ?_
    rw [show r⁻¹ * (w * r * w⁻¹) = r⁻¹ * w * r * w⁻¹ by group]
    exact h3
  have hmap : R.map (MulAut.conj w).toMonoidHom ≤ R := by
    rintro _ ⟨r, hr, rfl⟩
    exact hw1 r hr
  have heq : R.map (MulAut.conj w).toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj w).toMonoidHom
        (MulAut.conj w).injective).toEquiv])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem AData.normalizer_of_comm {c : A2Cfg G T M L D H K q} {t a : G} (hd : AData c t a)
    (hOR : pCoreOf 2 K ≤ pCoreOf 2 H) {w : G} (hwK : w ∈ K)
    (hwa : w * a * w⁻¹ * a⁻¹ ∈ pCoreOf 2 K) : w ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  refine mem_normalizer_of_key hOR fun r hr => ?_
  have haN : a ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hd.aK
  rcases hd.dich r hr with h1 | h2
  · exact (mem_kerAct.mp h1).2 w hwK
  · have h3 := (mem_kerAct.mp h2).2 w hwK
    have h4 : a * w * a⁻¹ * w⁻¹ ∈ pCoreOf 2 K := by
      have := (pCoreOf 2 K).inv_mem hwa
      simpa [mul_assoc] using this
    have e : r * w * r⁻¹ * w⁻¹ =
        a * ((a⁻¹ * r) * w * (a⁻¹ * r)⁻¹ * w⁻¹) * a⁻¹ * (a * w * a⁻¹ * w⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 K).mul_mem (conj_mem_pCoreOf_of_mem_normalizer haN h3) h4

theorem AData.actA_R_dich {c : A2Cfg G T M L D H K q} {t a : G} (hd : AData c t a)
    (hRN : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G)) {w : ↥K ⧸ CFSG.pCore 2 ↥K}
    (hw : w ∈ KAct.actA K (pCoreOf 2 H) hRN) :
    w = 1 ∨ w = (QuotientGroup.mk (⟨a, hd.aK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hinj := KAct.conj_injective_of_center_eq_bot (KAct.center_quot_eq_bot c)
  obtain ⟨r, hr⟩ := KAct.mem_actA_iff.mp hw
  have hrN : (r : G) ∈ Subgroup.normalizer (K : Set G) := hRN r.2
  have haN : a ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hd.aK
  rcases hd.dich r r.2 with h1 | h2
  · left
    have h := (L15420.quotConj_eq_one_iff hrN).mpr (fun k hk => (mem_kerAct.mp h1).2 k hk)
    apply hinj
    rw [map_one, ← hr]
    exact h
  · right
    have hu : L15420.quotConj K (a⁻¹ * r) (Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hrN) = 1 :=
      (L15420.quotConj_eq_one_iff _).mpr (fun k hk => (mem_kerAct.mp h2).2 k hk)
    rw [L15420.quotConj_mul (Subgroup.inv_mem _ haN) hrN, KAct.quotConj_inv_eq haN] at hu
    have h3 : L15420.quotConj K a haN = L15420.quotConj K r hrN := inv_mul_eq_one.mp hu
    apply hinj
    rw [← hr, ← L15420.quotConj_of_mem hd.aK]
    exact h3.symm

theorem AData.quotConj_eq_of_mem {c : A2Cfg G T M L D H K q} {t a : G} (hd : AData c t a) {r : G}
    (hrN : r ∈ Subgroup.normalizer (K : Set G)) (h2 : a⁻¹ * r ∈ kerAct K) :
    L15420.quotConj K r hrN = MulAut.conj
      (QuotientGroup.mk (⟨a, hd.aK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  have haN : a ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hd.aK
  have hu : L15420.quotConj K (a⁻¹ * r) (Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hrN) = 1 :=
    (L15420.quotConj_eq_one_iff _).mpr (fun k hk => (mem_kerAct.mp h2).2 k hk)
  rw [L15420.quotConj_mul (Subgroup.inv_mem _ haN) hrN, KAct.quotConj_inv_eq haN] at hu
  have h3 : L15420.quotConj K a haN = L15420.quotConj K r hrN := inv_mul_eq_one.mp hu
  rw [← h3]
  exact L15420.quotConj_of_mem hd.aK

theorem KCtx.quotConj_one_of_mem_K' {c : A2Cfg G T M L D H K q} {t : G} (ctx : KCtx c t) {u : G}
    (hu : u ∈ K.map (MulAut.conj t).toMonoidHom) :
    L15420.quotConj K u (ctx.K'N hu) = 1 := by
  refine (L15420.quotConj_eq_one_iff _).mpr fun l hl => ?_
  have h1 : ⁅l, u⁆ ∈ ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ := Subgroup.commutator_mem_commutator hl hu
  have h2 := (pCoreOf 2 K).inv_mem (ctx.comm h1)
  have e : u * l * u⁻¹ * l⁻¹ = (l * u * l⁻¹ * u⁻¹)⁻¹ := by group
  rw [e]
  exact h2

theorem A2Cfg.normalizer_Vp_le_normalizer_R
    (hG1 : Leaf_G1) (hG4 : Leaf_G4) (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) :
    a2G2 K T ⊓ Subgroup.normalizer (a2Vp L T H : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact c.nf.TK hcon
  have ctx := c.kctx h37 h38 ht htK
  obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
  obtain ⟨a, hd, hxa⟩ := c.exists_AData_of_x h5 h7 h9 h128 h37 h38 h39 ht hxY hxK hx3
  have hRN : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) := c.R_le_normalizer_K h37 h38
  have hOR : pCoreOf 2 K ≤ pCoreOf 2 H := c.pCoreOf_K_le_R h37 h38
  have hinj := KAct.conj_injective_of_center_eq_bot (KAct.center_quot_eq_bot c)
  have hTH : T ≤ H := c.sylow_H.1
  have hTR : ∀ s ∈ T, s ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := fun s hs =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hTH hs)
  obtain ⟨-, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hHN : H ≤ Subgroup.normalizer (a2Vp L T H : Set G) := fun h hh =>
    mem_normalizer_commutator_of ((sup_le hLV hTV) (c.nf.HLT hh)) (le_normalizer_oTwoUpper H hh)
  set N₀ : Subgroup G := a2G2 K T ⊓ Subgroup.normalizer (a2Vp L T H : Set G) with hN₀
  have hHN₀ : H ≤ N₀ := le_inf c.H_le_G2 hHN
  have hRN₀ : pCoreOf 2 H ≤ N₀ := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHN₀
  have hTN₀ : T ≤ N₀ := hTH.trans hHN₀
  set S : Subgroup G := N₀ ⊓ Subgroup.normalizer (K : Set G) with hS
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  set F := KAct.actA K S hSK with hFdef
  set xb : ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk (⟨x, hxK⟩ : ↥K) with hxb
  set ab : ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk (⟨a, hd.aK⟩ : ↥K) with habdef
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hxK
  have hxH : x ∈ H := CFSG.Quasithin.oTwoUpper_le H hxY
  have hxS : x ∈ S := ⟨hHN₀ hxH, hxN⟩
  have hxq : L15420.quotConj K x hxN = MulAut.conj xb := L15420.quotConj_of_mem hxK
  have hxF : xb ∈ F := KAct.mem_actA_iff.mpr ⟨⟨x, hxS⟩, hxq⟩
  obtain ⟨r₁, hr₁R, hr₁K⟩ := hd.nontriv
  have hr₁a : a⁻¹ * r₁ ∈ kerAct K := (hd.dich r₁ hr₁R).resolve_left hr₁K
  have hr₁S : r₁ ∈ S := ⟨hRN₀ hr₁R, hRN hr₁R⟩
  have haF : ab ∈ F :=
    KAct.mem_actA_iff.mpr ⟨⟨r₁, hr₁S⟩, hd.quotConj_eq_of_mem (hRN hr₁R) hr₁a⟩
  have haA : ab ∈ KAct.actA K (pCoreOf 2 H) hRN :=
    KAct.mem_actA_iff.mpr ⟨⟨r₁, hr₁R⟩, hd.quotConj_eq_of_mem (hRN hr₁R) hr₁a⟩
  obtain ⟨g, hgT, hg⟩ := c.exists_inverting_square
  obtain ⟨t₀, ht₀T, ht₀N, -, hKK, hs⟩ := c.kstruct h37 h38
  have hτT : g ^ 2 ∈ T := T.pow_mem hgT 2
  have hτK : g ^ 2 ∈ Subgroup.normalizer (K : Set G) :=
    KAct.sq_mem_normalizer_of_action rfl ht₀N hs ht₀T hgT
  have hτR : g ^ 2 ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := hTR _ hτT
  obtain ⟨sb, hsb⟩ := KAct.quot_eq_conj_of_induces c.inner
    (Subgroup.mem_inf.mpr ⟨hτT, hτK⟩) hτK
  have hτS : g ^ 2 ∈ S := ⟨hTN₀ hτT, hτK⟩
  have hsF : sb ∈ F := KAct.mem_actA_iff.mpr ⟨⟨g ^ 2, hτS⟩, hsb⟩
  have hsA : sb ∈ Subgroup.normalizer
      ((KAct.actA K (pCoreOf 2 H) hRN : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) :
        Set (↥K ⧸ CFSG.pCore 2 ↥K)) := KAct.mem_normalizer_actA hτK hτR hsb
  have hr₀ : g ^ 2 * x * (g ^ 2)⁻¹ * x ∈ pCoreOf 2 H := hg x hxY
  have hτx : g ^ 2 * x * (g ^ 2)⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hτK hxN) (Subgroup.inv_mem _ hτK)
  have hθ : KAct.actHom K (pCoreOf 2 H) hRN ⟨g ^ 2 * x * (g ^ 2)⁻¹ * x, hr₀⟩ =
      MulAut.conj (sb * xb * sb⁻¹ * xb) := by
    show L15420.quotConj K (g ^ 2 * x * (g ^ 2)⁻¹ * x) (hRN hr₀) = _
    rw [L15420.quotConj_mul hτx hxN, KAct.quotConj_conj_eq hτK hxN hτx, hsb, hxq]
    simp only [map_mul, map_inv]
  have hsxA : sb * xb * sb⁻¹ * xb ∈ KAct.actA K (pCoreOf 2 H) hRN :=
    KAct.mem_actA_iff.mpr ⟨_, hθ⟩
  have hsq2 : ∃ k : ℕ, sb ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := c.nf.hyp.sylow.1 ⟨g ^ 2, hτT⟩
    refine ⟨k, hinj ?_⟩
    have h1 : (⟨g ^ 2, hτK⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2 := congrArg (L15420.quotConjHom K) h1
    rw [map_pow, map_one] at h2
    have h3 : (MulAut.conj sb) ^ 2 ^ k = 1 := by
      rw [← hsb]
      exact h2
    rw [map_pow, map_one]
    exact h3
  obtain ⟨k₂, hk₂⟩ := hsq2
  have hsq : sb * sb = 1 := psl_two_elt_sq q c.q_prime c.q_mod c.model hk₂
  have hx3' : orderOf xb = 3 := KAct.orderOf_mk_eq_three hxK hx3
  have hab1 : ab ≠ 1 := fun h => hd.a_not (L15420.mk_eq_one_iff.mp h)
  have hab2 : ab * ab = 1 := by
    have h1 : (QuotientGroup.mk ((⟨a, hd.aK⟩ : ↥K) ^ 2) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 :=
      L15420.mk_eq_one_iff.mpr hd.a_sq
    rw [QuotientGroup.mk_pow] at h1
    rw [← pow_two]
    exact h1
  have hab : orderOf ab = 2 := orderOf_eq_prime (by rw [pow_two]; exact hab2) hab1
  have hxa' : ab * xb = xb * ab := by
    have h1 : (QuotientGroup.mk ((⟨x, hxK⟩ : ↥K) * ⟨a, hd.aK⟩ * (⟨x, hxK⟩ : ↥K)⁻¹ *
        (⟨a, hd.aK⟩ : ↥K)⁻¹) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      apply L15420.mk_eq_one_iff.mpr
      have := hxa
      rw [commutatorElement_def] at this
      simpa using this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    have h2 : xb * ab * xb⁻¹ = ab := by
      calc xb * ab * xb⁻¹ = (xb * ab * xb⁻¹ * ab⁻¹) * ab := by group
        _ = ab := by rw [h1, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  obtain ⟨hsa, hsx, hs1⟩ := dih_relations (KAct.actA K (pCoreOf 2 H) hRN) xb ab sb
    (fun w hw => hd.actA_R_dich hRN hw) hab1 hab2 haA hx3' hxa' hsA hsxA
  have hFtop : F ≠ ⊤ := by
    intro hFt
    have hq5 : 5 ≤ q := by
      have := c.q_mod
      have := c.q_prime.two_le
      omega
    haveI hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
      isSimpleGroup_of_psl_two_model hq5 c.model
    let J : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
      ((K ⊓ N₀).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
    have hJn : J.Normal := by
      refine ⟨fun n hn w => ?_⟩
      obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hn
      have hw : w ∈ F := by rw [hFt]; exact Subgroup.mem_top w
      obtain ⟨u, hu⟩ := KAct.mem_actA_iff.mp hw
      have hku : (k' : G) ∈ K ⊓ N₀ := Subgroup.mem_subgroupOf.mp hk'
      have h1 : w * (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k') * w⁻¹ =
          L15420.quotConj K (u : G) (hSK u.2) (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k') := by
        have := congrArg (fun φ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) =>
          φ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k')) hu
        simp only [KAct.actHom_apply, MulAut.conj_apply] at this
        exact this.symm
      rw [h1]
      show L15420.quotConj K (u : G) (hSK u.2) (QuotientGroup.mk k') ∈ J
      rw [L15420.quotConj_mk]
      refine Subgroup.mem_map.mpr ⟨L15420.conjRestr K (u : G) (hSK u.2) k', ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf, L15420.conjRestr_apply_coe]
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hSK u.2) k').mp k'.2, ?_⟩
      have hu0 : (u : G) ∈ N₀ := u.2.1
      exact N₀.mul_mem (N₀.mul_mem hu0 hku.2) (N₀.inv_mem hu0)
    haveI := hJn
    rcases hsimple.eq_bot_or_eq_top_of_normal J with hJ | hJ
    ·
      have hxJ : xb ∈ J := Subgroup.mem_map.mpr
        ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr ⟨hxK, hHN₀ hxH⟩, rfl⟩
      rw [hJ, Subgroup.mem_bot] at hxJ
      have : orderOf xb = 1 := by rw [hxJ]; exact orderOf_one
      omega
    ·
      apply c.not_K_le_normalizer_Vp hG1 h36 h5 h7 h9 hGA h128 h37 h38 h39
      intro k hk
      have hkJ : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ J := by
        rw [hJ]; exact Subgroup.mem_top _
      obtain ⟨k₁, hk₁, hk₁k⟩ := Subgroup.mem_map.mp hkJ
      have hk₁N : (k₁ : G) ∈ N₀ := (Subgroup.mem_subgroupOf.mp hk₁).2
      have hk₁k' : (QuotientGroup.mk k₁ : ↥K ⧸ CFSG.pCore 2 ↥K) = QuotientGroup.mk ⟨k, hk⟩ := hk₁k
      have hmem : (k₁ : G)⁻¹ * k ∈ pCoreOf 2 K := KAct.mk_eq_iff_coe.mp hk₁k'
      have e : k = (k₁ : G) * ((k₁ : G)⁻¹ * k) := by group
      have : k ∈ N₀ := by
        rw [e]
        exact N₀.mul_mem hk₁N (hRN₀ (hOR hmem))
      exact this.2
  have hFcent : F ≤ Subgroup.centralizer ({ab} : Set (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    nfa2_g4_apply hG4 c.q_prime c.q_mod c.model xb ab sb hx3' hab hxa' hsa hsx hsq hs1 F hxF haF
      hsF hFtop
  have hKnorm : ∀ (k : G) (hk : k ∈ K) (u : G) (hu : u ∈ S),
      L15420.quotConj K u (hSK hu) = MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) →
        k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    intro k hk u hu hq
    have hkF : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ F :=
      KAct.mem_actA_iff.mpr ⟨⟨u, hu⟩, hq⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (hFcent hkF) ab (Set.mem_singleton _)
    apply hd.normalizer_of_comm hOR hk
    have h2 : (QuotientGroup.mk ((⟨k, hk⟩ : ↥K) * ⟨a, hd.aK⟩ * (⟨k, hk⟩ : ↥K)⁻¹ *
        (⟨a, hd.aK⟩ : ↥K)⁻¹) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← habdef]
      calc _ = (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) * ab *
            (QuotientGroup.mk (⟨k, hk⟩ : ↥K))⁻¹ * ab⁻¹ := rfl
        _ = 1 := by
          rw [← h1]
          group
    have h3 := L15420.mk_eq_one_iff.mp h2
    simpa using h3
  have hK0N : conjClosure K T ≤ Subgroup.normalizer (K : Set G) := by
    rw [ctx.K0]
    exact sup_le Subgroup.le_normalizer ctx.K'N
  have hK'perm : ∀ k' ∈ K.map (MulAut.conj t).toMonoidHom, t * k' * t⁻¹ ∈ K := by
    intro k' hk'
    rcases ctx.perm t ht with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (A38.map_conj_eq_iff.mp h1) htK
    · rw [← h2]
      exact ⟨k', hk', by simp [MulAut.conj_apply]⟩
  have hK0 : ∀ n ∈ conjClosure K T, n ∈ N₀ → n ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    intro n hn hnN
    have hn' : n ∈ ((K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
      rw [← ctx.K0]; exact hn
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K _ ctx.K'N, Set.mem_mul] at hn'
    obtain ⟨k, hk, k', hk', rfl⟩ := hn'
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
    have hk'N : k' ∈ Subgroup.normalizer (K : Set G) := ctx.K'N hk'
    have hnS : k * k' ∈ S := ⟨hnN, Subgroup.mul_mem _ hkN hk'N⟩
    have hq1 : L15420.quotConj K (k * k') (hSK hnS) =
        MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) := by
      rw [L15420.quotConj_mul hkN hk'N, ctx.quotConj_one_of_mem_K' hk', mul_one]
      exact L15420.quotConj_of_mem hk
    have hkR := hKnorm k hk (k * k') hnS hq1
    have hk₁ : t * k' * t⁻¹ ∈ K := hK'perm k' hk'
    have hk₁' : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    have hk₁N : t * k * t⁻¹ ∈ Subgroup.normalizer (K : Set G) := ctx.K'N hk₁'
    have hk₂N : t * k' * t⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk₁
    have hnt : t * (k * k') * t⁻¹ ∈ N₀ :=
      N₀.mul_mem (N₀.mul_mem (hTN₀ ht) hnN) (N₀.inv_mem (hTN₀ ht))
    have hntS : (t * k * t⁻¹) * (t * k' * t⁻¹) ∈ S := by
      refine ⟨?_, Subgroup.mul_mem _ hk₁N hk₂N⟩
      have e : (t * k * t⁻¹) * (t * k' * t⁻¹) = t * (k * k') * t⁻¹ := by group
      rw [e]
      exact hnt
    have hq2 : L15420.quotConj K ((t * k * t⁻¹) * (t * k' * t⁻¹)) (hSK hntS) =
        MulAut.conj (QuotientGroup.mk (⟨t * k' * t⁻¹, hk₁⟩ : ↥K)) := by
      rw [L15420.quotConj_mul hk₁N hk₂N, ctx.quotConj_one_of_mem_K' hk₁', one_mul]
      exact L15420.quotConj_of_mem hk₁
    have hk'R : t * k' * t⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      hKnorm (t * k' * t⁻¹) hk₁ _ hntS hq2
    have hk'R' : k' ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
      have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTR t ht)) hk'R)
        (hTR t ht)
      have e : t⁻¹ * (t * k' * t⁻¹) * t = k' := by group
      rwa [e] at h1
    exact Subgroup.mul_mem _ hkR hk'R'
  intro n hn
  have hnG : n ∈ ((conjClosure K T ⊔ T : Subgroup G) : Set G) := hn.1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (conjClosure K T) T
    (le_normalizer_conjClosure K T), Set.mem_mul] at hnG
  obtain ⟨k₀, hk₀, t', ht', rfl⟩ := hnG
  have hk₀N : k₀ ∈ N₀ := by
    have h1 : k₀ = (k₀ * t') * t'⁻¹ := by group
    rw [h1]
    exact N₀.mul_mem hn (N₀.inv_mem (hTN₀ ht'))
  exact Subgroup.mul_mem _ (hK0 k₀ hk₀ hk₀N) (hTR t' ht')

end CFSG.Quasithin.H13.NFa2
