module

public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec83UpperModule
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial
public import CFSG.RankThree.GF2n.Stroth80.AddAutDescent
public import CFSG.RankThree.GF2n.Stroth80.Sec8Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.F2Fixed (fixedSub mem_fixedSub)
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec83up_main (h34 : Stroth34Statement) (h53 : Stroth53Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hs : Sec5Hyp hc n t) (hr : Sec7A hc t r) (hpts : Sec8Pts hc t r m K φ u u')
    (hM6 : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅ρ, w⁆ ∈ Sec8W1 M Q Z B t r)
    {s : G} (hsR : s ∈ Rt M (LB M Q B) t) (hsc : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅s, ρ⁆ ∈ Q) :
    Nat.card ↥(Ut Q Z s) ≤ Nat.card Z ^ (2 * m + 1) := by
  classical
  haveI := hpts.charP
  have h8 : Sec8Hyp hc n t := ⟨hs, m, hpts.two_le, hpts.spMNat⟩
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hrR
  have hinv := sec8InvStatement_holds G M Q Z B hc n t h8 r hr
  obtain ⟨hV1c, hWc, -⟩ := h53.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane
    (conjSubgroup r B) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    (Sec8V1 M Q Z B t r) (Sec8W1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hd := h53.2.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have he := h53.2.2.2.2 G M Q Z B hc n t hs hpts.spNat (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  have hsN : s ∈ hc.CN t := by
    obtain ⟨Z0, hZ0⟩ := exists_isCentrePre (hc.Q_le_Rt hs.mem)
    exact sec8_Z0_le_CN hc h8 hZ0 ((hZ0 s).mpr ⟨hsR, hsc⟩)
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q := fun ρ hρ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM hρ)) x).mp hx
  have hnormZ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Z, ρ * x * ρ⁻¹ ∈ Z := fun ρ hρ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hRM hρ)) x).mp hx
  have hcommQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, ⁅ρ, x⁆ ∈ Q := fun ρ hρ x hx => by
    rw [commutatorElement_def]
    exact Q.mul_mem (hnormQ ρ hρ x hx) (Q.inv_mem hx)
  have hSec : SecHyp (Rt M (LB M Q B) t) Q Z :=
    ⟨hZQ, fun x hx y hy => hc.hyp.toHyp79.comm_mem_V hx hy,
      fun x hx => hc.hyp.toHyp79.sq_mem_V hx, hnormQ, hnormZ⟩
  obtain ⟨Md, _, _, κ, hκ⟩ := exists_sectionModule hSec
  haveI : Finite Md := hκ.finite
  obtain ⟨ε, hε1, hεR⟩ := exists_comm_endo hc hRM hκ (hRM hsR) (fun ρ hρ => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hsc ρ⁻¹ ((Rt M (LB M Q B) t).inv_mem hρ)))
  have hV1ε : ∀ a ∈ secSub κ (Sec8V1 M Q Z B t r), ε a = 0 := by
    intro a ha
    obtain ⟨x, hxV₁, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    rw [← hxa', hε1 x]
    have hZ : ⁅(x : G), s⁆ ∈ Z := by
      rw [← commutatorElement_inv]
      exact Z.inv_mem (hd.1 s hsN x hxV₁)
    have : κ ⟨⁅(x : G), s⁆, hc.comm_mem_Q (hRM hsR) x.2⟩ = 1 := (hκ.ker _).mpr hZ
    rw [this]
    rfl
  obtain ⟨hVA1, hA1W, hVA2, hA2W, hsup, -, -, -, hA1c, hA2c⟩ := hcd
  have hW₁Q : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  have hV₁Q : Sec8V1 M Q Z B t r ≤ Q := inf_le_left.trans (sup_le inf_le_left hVQ)
  have hA1 : ∀ a ∈ secSub κ (QB B ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r),
      ∀ l ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t),
      l • a - a ∈ secSub κ (Sec8V1 M Q Z B t r) := by
    intro a ha l hl
    obtain ⟨x, hxA, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    have hlx : ⁅(l : G), (x : G)⁆ ∈ Sec8V1 M Q Z B t r :=
      (hA1c x (hA1W hxA)).mp hxA l (Subgroup.mem_subgroupOf.mp hl)
    rw [← hxa', smul_toAdd_sub_eq hκ hnormQ l x (hcommQ l l.2 x x.2)]
    exact mem_secSub.mpr ⟨⟨⁅(l : G), (x : G)⁆, hcommQ l l.2 x x.2⟩, hlx, rfl⟩
  have hA2 : ∀ a ∈ secSub κ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r),
      ∀ l ∈ (LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t),
      l • a - a ∈ secSub κ (Sec8V1 M Q Z B t r) := by
    intro a ha l hl
    obtain ⟨x, hxA, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    have hlx : ⁅(l : G), (x : G)⁆ ∈ Sec8V1 M Q Z B t r :=
      (hA2c x (hA2W hxA)).mp hxA l (Subgroup.mem_subgroupOf.mp hl)
    rw [← hxa', smul_toAdd_sub_eq hκ hnormQ l x (hcommQ l l.2 x x.2)]
    exact mem_secSub.mpr ⟨⟨⁅(l : G), (x : G)⁆, hcommQ l l.2 x x.2⟩, hlx, rfl⟩
  have hW1 : secSub κ (Sec8W1 M Q Z B t r) =
      secSub κ (QB B ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r) ⊔
        secSub κ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r) := by
    rw [← secSub_sup (hA1W.trans hW₁Q) (hA2W.trans hW₁Q), hsup]
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have h35B := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have h35C := (stroth_3_5 h34 hcC hs.width hs.n_gt (hc.noA2_conj hs.noA2 hrM)
    (hs.gen.conj_of_mem hrM)).2.1
  have hF₁ : ∀ b : Md, (∀ l ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t), l • b = b) →
      b ∈ secSub κ (B ⊔ Z) := by
    intro b hb
    have hmem : b ∈ fixedSub Md (((LB M Q B).subgroupOf (Rt M (LB M Q B) t) :
        Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t)) :=
      mem_fixedSub.mpr fun x hx => hb x hx
    obtain ⟨x, hxb, hxc⟩ := (mem_fixedSub_iff hnormQ hκ hLR).mp hmem
    have hx : (x : G) ∈ CQt Q Z (LB M Q B) := ⟨x.2, fun l hl => hxc l hl⟩
    rw [h35B] at hx
    exact mem_secSub.mpr ⟨x, hx, hxb⟩
  have hF₂ : ∀ b : Md, (∀ l ∈ (LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t),
      l • b = b) → b ∈ secSub κ (conjSubgroup r B ⊔ Z) := by
    intro b hb
    have hmem : b ∈ fixedSub Md (((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t) :
        Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t)) :=
      mem_fixedSub.mpr fun x hx => hb x hx
    obtain ⟨x, hxb, hxc⟩ := (mem_fixedSub_iff hnormQ hκ hL'R).mp hmem
    have hx : (x : G) ∈ CQt Q Z (LB M Q (conjSubgroup r B)) := ⟨x.2, fun l hl => hxc l hl⟩
    rw [h35C] at hx
    exact mem_secSub.mpr ⟨x, hx, hxb⟩
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hBZV : B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le (hc.B_le_Vt hs.mem) sec39_Z_le_Vt
  have hCZV : conjSubgroup r B ⊔ Z ≤ Vt M (LB M Q B) B Z t := hc.conj_Rt_le_Vt hs.mem hrR
  have hBcard : Nat.card B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hCcard : Nat.card (conjSubgroup r B) = Nat.card Z := by
    rw [card_conjSubgroup, hBcard]
  have hcardF₁ : Nat.card ↥(secSub κ (B ⊔ Z)) ≤ Nat.card Z := by
    have h1 := natCard_secSub_mul hZQ hκ (le_sup_right : Z ≤ B ⊔ Z) (sup_le hc.le hZQ)
    rw [hc.card_sup_Z, hBcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).le
  have hcardF₂ : Nat.card ↥(secSub κ (conjSubgroup r B ⊔ Z)) ≤ Nat.card Z := by
    have h1 := natCard_secSub_mul hZQ hκ (le_sup_right : Z ≤ conjSubgroup r B ⊔ Z)
      (sup_le hcC.le hZQ)
    rw [hcC.card_sup_Z, hCcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).le
  have hirrG : ∀ U : Subgroup G, Z ≤ U → U ≤ Vt M (LB M Q B) B Z t →
      (∀ ρ ∈ Rt M (LB M Q B) t, ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U) → U = Z ∨ U = Vt M (LB M Q B) B Z t :=
    fun U hZU hUV hRU => hpts.naturalRep.eq_or_eq_of_invariant natIrred_statedSp
      addCommutantScalar_statedSp hZU hUV hRU
  have hirr := secSub_irred_of_irred hκ sec39_Z_le_Vt hVQ hnormQ hirrG
  have hcardV : Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ (2 * m) := by
    have h1 := natCard_secSub_mul hZQ hκ sec39_Z_le_Vt hVQ
    rw [hpts.card_V, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hm2 := hpts.two_le
  have hqq : Nat.card Z * Nat.card Z < Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) := by
    rw [hcardV, ← pow_two]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hq : Nat.card Z < Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) := by
    rw [hcardV]
    calc Nat.card Z = Nat.card Z ^ 1 := (pow_one _).symm
      _ < Nat.card Z ^ (2 * m) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hinvW1 : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ secSub κ (Sec8W1 M Q Z B t r),
      z • a ∈ secSub κ (Sec8W1 M Q Z B t r) := by
    intro z a ha
    have h1 := secSub_conjSubgroup hnormQ hκ z (Sec8W1 M Q Z B t r)
    rw [(hinv z z.2).2] at h1
    have : z • a ∈ (secSub κ (Sec8W1 M Q Z B t r)).map (DistribSMul.toAddMonoidHom Md z) :=
      ⟨a, ha, rfl⟩
    rwa [← h1] at this
  have hinvW : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ secSub κ (Wt Q (Vt M (LB M Q B) B Z t)),
      z • a ∈ secSub κ (Wt Q (Vt M (LB M Q B) B Z t)) := by
    intro z a ha
    have h0 : conjSubgroup (z : G) (Wt Q (Vt M (LB M Q B) B Z t)) =
        Wt Q (Vt M (LB M Q B) B Z t) :=
      sec8_conjSubgroup_eq_of_mem_normalizer (sec8_Wt_mem_normalizer
        (hc.hyp.Q_normal.2 (hRM z.2)) (hc.Rt_normalizes_Vt hs.mem z.2))
    have h1 := secSub_conjSubgroup hnormQ hκ z (Wt Q (Vt M (LB M Q B) B Z t))
    rw [h0] at h1
    have : z • a ∈ (secSub κ (Wt Q (Vt M (LB M Q B) B Z t))).map
        (DistribSMul.toAddMonoidHom Md z) := ⟨a, ha, rfl⟩
    rwa [← h1] at this
  have hε0W1 : ∀ a ∈ secSub κ (Sec8W1 M Q Z B t r), ε a = 0 :=
    eps_kills_sW1 ε hεR hV1ε hA1 hA2 hW1 hF₁ hF₂ (secSub_mono hBZV) (secSub_mono hCZV)
      hcardF₁ hcardF₂ hirr hqq hinvW1
  have hW' : ∀ a ∈ secSub κ (Wt Q (Vt M (LB M Q B) B Z t)),
      ∀ l ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t),
      l • a - a ∈ secSub κ (Sec8W1 M Q Z B t r) := by
    intro a ha l hl
    obtain ⟨x, hxW, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    rw [← hxa', smul_toAdd_sub_eq hκ hnormQ l x (hcommQ l l.2 x x.2)]
    exact mem_secSub.mpr ⟨⟨⁅(l : G), (x : G)⁆, hcommQ l l.2 x x.2⟩, hM6 l l.2 x hxW, rfl⟩
  have hε0W : ∀ a ∈ secSub κ (Wt Q (Vt M (LB M Q B) B Z t)), ε a = 0 :=
    eps_kills_sW ε hεR hε0W1 hW' hF₁ (secSub_mono hBZV) hcardF₁ hirr hq hinvW
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun z hz => ⟨hZQ hz,
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm⟩
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hker : secSub κ (Wt Q (Vt M (LB M Q B) B Z t)) ≤ ε.ker := fun a ha => hε0W a ha
  obtain ⟨Uε, hZUε, hUεQ, hUε⟩ := exists_secSub_eq hZQ hκ ε.range
  have hεinv : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ secSub κ Uε, z • a ∈ secSub κ Uε := by
    intro z a ha
    rw [hUε] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    exact ⟨z • b, hεR z b⟩
  have hUεR := conj_mem_of_secSub_invariant hκ hnormQ hZUε hUεQ hεinv
  have hUt : Ut Q Z s ≤ Uε := by
    refine sup_le ?_ hZUε
    refine commutator_zpowers_le (sec8_le_normalizer_of_conj hUεR hsR) fun x hx => ?_
    have hxs : ⁅x, s⁆ ∈ Q := hc.comm_mem_Q (hRM hsR) hx
    have h1 : Multiplicative.toAdd (κ ⟨⁅x, s⁆, hxs⟩) ∈ secSub κ Uε := by
      rw [hUε, ← hε1 ⟨x, hx⟩]
      exact ⟨_, rfl⟩
    exact (toAdd_mem_secSub_iff hκ hZUε _).mp h1
  have hcardUε : Nat.card ↥ε.range * Nat.card Z = Nat.card Uε := by
    have := natCard_secSub_mul hZQ hκ hZUε hUεQ
    rwa [hUε] at this
  have hmd := natCard_eq_of_isSecMod hZQ hκ
  have hsW := natCard_secSub_mul hZQ hκ hZW hWQ
  obtain ⟨-, hN, -⟩ := hpts.act
  haveI := hN
  have hchi' := card_mul_card_of_isChiIso he hWQ (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t)
  have hrk := AddSubgroup.card_ker_mul_card_range ε
  have hkle : Nat.card ↥(secSub κ (Wt Q (Vt M (LB M Q B) B Z t))) ≤ Nat.card ↥ε.ker :=
    AddSubgroup.card_le_of_le hker
  have hkey : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * (Nat.card ↥ε.range * Nat.card Z) ≤
      Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(Vt M (LB M Q B) B Z t) := by
    calc Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * (Nat.card ↥ε.range * Nat.card Z)
        = (Nat.card ↥(secSub κ (Wt Q (Vt M (LB M Q B) B Z t))) * Nat.card Z) *
            (Nat.card ↥ε.range * Nat.card Z) := by rw [hsW]
      _ ≤ (Nat.card ↥ε.ker * Nat.card Z) * (Nat.card ↥ε.range * Nat.card Z) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hkle)
      _ = (Nat.card ↥ε.ker * Nat.card ↥ε.range) * Nat.card Z * Nat.card Z := by ring
      _ = Nat.card Md * Nat.card Z * Nat.card Z := by rw [hrk]
      _ = Nat.card Q * Nat.card Z := by rw [hmd]; ring
      _ = Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(Vt M (LB M Q B) B Z t) := hchi'
  have hr_le : Nat.card ↥ε.range * Nat.card Z ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) :=
    Nat.le_of_mul_le_mul_left hkey Nat.card_pos
  calc Nat.card ↥(Ut Q Z s) ≤ Nat.card Uε := Subgroup.card_le_of_le hUt
    _ = Nat.card ↥ε.range * Nat.card Z := hcardUε.symm
    _ ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) := hr_le
    _ = Nat.card Z ^ (2 * m + 1) := hpts.card_V

theorem sec83up_R_trivial (h53 : Stroth53Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hs : Sec5Hyp hc n t) (hr : Sec7A hc t r) (hpts : Sec8Pts hc t r m K φ u u') :
    ∀ ρ ∈ Rt M (LB M Q B) t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅ρ, w⁆ ∈ Sec8W1 M Q Z B t r := by
  classical
  haveI := hpts.charP
  have h8 : Sec8Hyp hc n t := ⟨hs, m, hpts.two_le, hpts.spMNat⟩
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hinv := sec8InvStatement_holds G M Q Z B hc n t h8 r hr
  obtain ⟨-, hWc, -⟩ := h53.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane
    (conjSubgroup r B) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    (Sec8V1 M Q Z B t r) (Sec8W1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hd := h53.2.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hV1V : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := le_inf le_sup_right le_sup_right
  have hV₁Q : Sec8V1 M Q Z B t r ≤ Q := inf_le_left.trans (sup_le inf_le_left hVQ)
  have hW₁W : Sec8W1 M Q Z B t r ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    inf_le_inf_left Q (Subgroup.centralizer_le hV1V)
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hZW₁ : Z ≤ Sec8W1 M Q Z B t r := fun z hz => ⟨hZQ hz,
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hV₁Q hv)).symm⟩
  have hnormW : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ρ * x * ρ⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun ρ hρ x hx =>
    conj_mem_of_conjSubgroup_eq (sec8_conjSubgroup_eq_of_mem_normalizer
      (sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 (hRM hρ)) (hc.Rt_normalizes_Vt hs.mem hρ))) hx
  have hnormW1 : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8W1 M Q Z B t r,
      ρ * x * ρ⁻¹ ∈ Sec8W1 M Q Z B t r := fun ρ hρ x hx =>
    conj_mem_of_conjSubgroup_eq (hinv ρ hρ).2 hx
  have hSec : SecHyp (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t)) (Sec8W1 M Q Z B t r) :=
    ⟨hW₁W, fun x hx y hy => hZW₁ (hc.hyp.toHyp79.comm_mem_V (hWQ hx) (hWQ hy)),
      fun x hx => hZW₁ (hc.hyp.toHyp79.sq_mem_V (hWQ hx)), hnormW, hnormW1⟩
  obtain ⟨Y₂, _, _, κ, hκ⟩ := exists_sectionModule hSec
  haveI : Finite Y₂ := hκ.finite
  have hcardY : Nat.card Y₂ ≤ Nat.card K := by
    have h1 := natCard_eq_of_isSecMod hW₁W hκ
    rw [hWc] at h1
    have h2 : Nat.card Z = Nat.card Y₂ := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [hpts.card, ← h2]
  have hkerAct : ∀ x ∈ φ.ker, ∀ a : Y₂, x • a = a := by
    intro x hx a
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    have hwa : Multiplicative.toAdd (κ w) = a := by rw [hw]; rfl
    have hxN : (x : G) ∈ hc.CN t := by
      rw [hpts.ker] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have hxw : ⁅(x : G), (w : G)⁆ ∈ Sec8W1 M Q Z B t r := hd.2.1 (x : G) hxN w (hWQ w.2)
    have hxwW' : ⁅(x : G), (w : G)⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      rw [commutatorElement_def]
      exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem (hnormW x x.2 w w.2)
        ((Wt Q (Vt M (LB M Q B) B Z t)).inv_mem w.2)
    have h1 := smul_toAdd_sub_eq hκ hnormW x w hxwW'
    have h2 : κ ⟨⁅(x : G), (w : G)⁆, hxwW'⟩ = 1 := (hκ.ker _).mpr hxw
    rw [h2, toAdd_one, sub_eq_zero] at h1
    rw [← hwa]
    exact h1
  obtain ⟨π, hπ⟩ := exists_addAut_hom_of_range φ hpts.range hkerAct
  have hπ1 : π = 1 := hom_statedSp_to_addAut_trivial hκ.two hcardY π
  intro ρ hρ w hw
  have hρw : ⁅ρ, w⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    rw [commutatorElement_def]
    exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem (hnormW ρ hρ w hw)
      ((Wt Q (Vt M (LB M Q B) B Z t)).inv_mem hw)
  have hall : ∀ a : Y₂, (⟨ρ, hρ⟩ : ↥(Rt M (LB M Q B) t)) • a = a := by
    intro a
    have hx : φ ⟨ρ, hρ⟩ ∈ StatedSp m K := by
      rw [← hpts.range]
      exact ⟨_, rfl⟩
    rw [← hπ _ hx a, hπ1]
    rfl
  have h1 := smul_toAdd_sub_eq hκ hnormW ⟨ρ, hρ⟩ ⟨w, hw⟩ hρw
  rw [hall, sub_self] at h1
  exact (hκ.ker _).mp (Multiplicative.toAdd.injective h1.symm)

theorem sec83Upper_of_53 (h34 : Stroth34Statement) (h53 : Stroth53Statement)
    (hA : Sec8AExistsStatement) (hPts : Sec5NatPointsSpStatement) :
    Sec83UpperStatement := by
  intro G _ _ M Q Z B hc n t m hs hm hsp s hsR hsc
  have h8 : Sec8Hyp hc n t := ⟨hs, m, hm, hsp⟩
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t h8
  obtain ⟨K, _, _, hK, m', hm', φ, u, u', hrange, hker, hact, huu', hL, hL'⟩ :=
    hPts G M Q Z B hc n t hs h8.spNat r hr.mem hr.plane
  have hpts : Sec8Pts hc t r m' K φ u u' := ⟨hm', hK, hrange, hker, hact, huu', hL, hL'⟩
  obtain rfl : m' = m := hpts.spMNat.m_unique hsp
  exact sec83up_main h34 h53 hs hr hpts (sec83up_R_trivial h53 hs hr hpts) hsR hsc

end CFSG.RankThree.GF2n.Stroth80
