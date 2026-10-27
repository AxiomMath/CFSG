module

public import CFSG.RankThree.GF2n.Stroth80.Sec92Split0
public import CFSG.RankThree.GF2n.Stroth80.Sec92SplitY
import CFSG.RankThree.GF2n.Stroth80.Sec92Quot
import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreV
public import CFSG.RankThree.GF2n.Stroth80.Sec3Action
public import CFSG.RankThree.GF2n.Stroth80.Sec9Stmt
import CFSG.RankThree.GF2n.Stroth80.HeringSec91QB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace Split92

theorem mem_Z_of_comm_R₀ {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G}
    (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t) {y : G} (hyV : y ∈ Vt M (LB M Q B) B Z t)
    (hy : ∀ e ∈ Sec9R0 hc t x, ⁅e, y⁆ ∈ Z) : y ∈ Z := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hR₀R : Sec9R0 hc t x ≤ Rt M (LB M Q B) t := Sec9R0_le_Rt hc hxR
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  let U : Subgroup G :=
    { carrier := {v | v ∈ Vt M (LB M Q B) B Z t ∧ ∀ e ∈ Sec9R0 hc t x, ⁅e, v⁆ ∈ Z}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(Vt M (LB M Q B) B Z t).mul_mem ha hb, fun e he => ?_⟩
        have e1 : ⁅e, a * b⁆ = ⁅e, a⁆ * (a * ⁅e, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact Z.mul_mem (ha' e he) (hZn _ (hQM (hVQ ha)) _ (hb' e he))
      one_mem' := ⟨(Vt M (LB M Q B) B Z t).one_mem, fun e _ => by
        simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(Vt M (LB M Q B) B Z t).inv_mem ha, fun e he => ?_⟩
        have e1 : ⁅e, a⁻¹⁆ = a⁻¹ * ⁅e, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e1]
        have := hZn _ (M.inv_mem (hQM (hVQ ha))) _ (Z.inv_mem (ha' e he))
        simpa using this }
  have hZU : Z ≤ U := fun z hz => ⟨sec39_Z_le_Vt hz, fun e he => by
    have h1 := HS9.Rt_cent_Z91 hc t (hR₀R he) hz
    rw [commutatorElement_def, h1, mul_inv_cancel]
    exact Z.one_mem⟩
  have hUV : U ≤ Vt M (LB M Q B) B Z t := fun v hv => hv.1
  have hRU : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U := by
    rintro ρ hρ u ⟨hu, hu'⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) u).mp hu,
      fun e he => ?_⟩
    have he' : ρ⁻¹ * e * ρ⁻¹⁻¹ ∈ Sec9R0 hc t x :=
      Sec9R0_conj_mem hc ht ((Rt M (LB M Q B) t).inv_mem hρ) he
    have e1 : ⁅e, ρ * u * ρ⁻¹⁆ = ρ * ⁅ρ⁻¹ * e * ρ⁻¹⁻¹, u⁆ * ρ⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact hZn _ (hc.Rt_le_M t hρ) _ (hu' _ he')
  rcases HS9.sec9VtIrred91 hs hZU hUV hRU with h | h
  · have : y ∈ U := ⟨hyV, hy⟩
    rw [h] at this
    exact this
  · exfalso
    apply hxN
    refine Ctx.mem_CN.mpr ⟨hxR, fun v hv => ?_⟩
    have hvU : v ∈ U := by rw [h]; exact hv
    exact hvU.2 x (mem_Sec9R0 hc t hxR)

theorem sec92_alpha (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) {x : G} (hxL : x ∈ LB M Q B)
    (hxN : x ∉ hc.CN t)
    (hxW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z)
    (ψ : ↥(Rt M (LB M Q B) t) →* ↥(StatedSL 2 K) × ↥(StatedSL 2 K))
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    (hψR₀ : ∀ g : ↥(Rt M (LB M Q B) t), (g : G) ∈ Sec9R0 hc t x ↔ (ψ g).2 = 1) :
    (∀ g : ↥(Rt M (LB M Q B) t), (ψ g).1 = 1 → ∀ m ∈ hc.CN t,
        ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅(g : G) * m * (g : G)⁻¹ * m⁻¹, w⁆ ∈ Z) ∧
    (∀ m ∈ hc.CN t, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅m, w⁆ ∈ Z) →
      ∃ a ∈ LB M Q B ⊓ hc.CN t, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅a, w⁆ ∈ Z) ∧
        ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
          (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅b, w⁆ ∈ Z) ∧ m = a * b) := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcA : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := sec9_CN_le_Rt hc t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLAR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hr.gen]; exact le_sup_right
  have hxR : x ∈ Rt M (LB M Q B) t := hLR hxL
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have h91b : Stroth91bStatement := stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)
  have hNW : ∀ s ∈ hc.CN t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t :=
    (h91b G M Q Z B hc n t hs r hr _ _ rfl rfl).2
  have hR₀W := Sec9R0_comm_mem hc ht hNW hxR hxW
  obtain ⟨hprod, -, -⟩ := sec9_N51 h34 h311a hNC hs hr
  obtain ⟨d, γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, -⟩ := exists_actionHom_H0 hc.hyp hM
  set ρ : ↥(Rt M (LB M Q B) t) →* (M₀.E ≃ₗ[GaloisField 2 d] M₀.E) :=
    φ.comp (Subgroup.inclusion (hc.Rt_le_H0 t)) with hρdef
  have hρπ : ∀ (g : ↥(Rt M (LB M Q B) t)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = ρ g (M₀.π y) :=
    fun g y hy => hφπ (Subgroup.inclusion (hc.Rt_le_H0 t) g) y hy
  have hρQ : ∀ g : ↥(Rt M (LB M Q B) t), ρ g = 1 ↔ (g : G) ∈ Q := fun g =>
    hφQ (Subgroup.inclusion (hc.Rt_le_H0 t) g)
  have hcQ : ∀ (g : ↥(Rt M (LB M Q B) t)) (y : G), y ∈ Q → ⁅(g : G), y⁆ ∈ Q := fun g y hy => by
    rw [commutatorElement_def]; exact Q.mul_mem (hQn _ (hRM g.2) y hy) (Q.inv_mem hy)
  have hcomm : ∀ (g : ↥(Rt M (LB M Q B) t)) (y : G), y ∈ Q →
      ρ g (M₀.π y) - M₀.π y = M₀.π ⁅(g : G), y⁆ := by
    intro g y hy
    have hgy : (g : G) * y * (g : G)⁻¹ ∈ Q := hQn _ (hRM g.2) y hy
    rw [commutatorElement_def, M₀.π_mul _ hgy _ (Q.inv_mem hy), Tim79.QuadModel.pi_inv M₀ hy,
      hρπ g y hy, sub_eq_add_neg]
  have hfixW : ∀ g : ↥(Rt M (LB M Q B) t),
      (∀ w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)), ρ g w = w) ↔
        ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅(g : G), y⁆ ∈ Z := by
    intro g
    constructor
    · intro h y hy
      have h1 := h _ (Tim79.QuadModel.pi_mem_img M₀ hy (hWQ hy))
      rw [← M₀.π_ker _ (hcQ g y (hWQ hy)), ← hcomm g y (hWQ hy), h1, sub_self]
    · rintro h _ ⟨y, hy, hyQ, rfl⟩
      have h1 := (M₀.π_ker _ (hcQ g y hyQ)).mpr (h y hy)
      rw [← hcomm g y hyQ] at h1
      exact sub_eq_zero.mp h1
  have hmemN : ∀ m : ↥(Rt M (LB M Q B) t), m ∈ ψ.ker ↔ (m : G) ∈ (hc.CN t) := fun m => by
    rw [hψk, Subgroup.mem_subgroupOf]
  have hD : AlphaData ρ (M₀.img (Vt M (LB M Q B) B Z t))
      (M₀.img (Wt Q (Vt M (LB M Q B) B Z t))) ψ := by
    refine ⟨hψs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro g _ ⟨y, hy, hyQ, rfl⟩
      rw [← hρπ g y hyQ]
      exact Tim79.QuadModel.pi_mem_img M₀
        ((Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht g.2) y).mp hy)
        (hQn _ (hRM g.2) y hyQ)
    · rintro g _ ⟨y, hy, hyQ, rfl⟩
      rw [← hρπ g y hyQ]
      exact Tim79.QuadModel.pi_mem_img M₀ (sec9_conj_mem_Wt hc ht g.2 hy)
        (hQn _ (hRM g.2) y hyQ)
    · rintro m hm _ ⟨y, hy, hyQ, rfl⟩
      have h1 := (M₀.π_ker _ (hcQ m y hyQ)).mpr
        ((Ctx.mem_CN.mp ((hmemN m).mp hm)).2 y hy)
      rw [← hcomm m y hyQ] at h1
      exact sub_eq_zero.mp h1
    · rintro m hm _ ⟨y, hy, hyQ, rfl⟩
      rw [hcomm m y hyQ]
      exact Tim79.QuadModel.pi_mem_img M₀ (hNW _ ((hmemN m).mp hm) y hy) (hcQ m y hyQ)
    · rintro e he _ ⟨y, hy, hyQ, rfl⟩
      rw [hcomm e y hyQ]
      exact Tim79.QuadModel.pi_mem_img M₀ (hR₀W _ ((hψR₀ e).mpr he) y hy) (hcQ e y hyQ)
    · rintro _ ⟨y, hy, hyQ, rfl⟩ hfix
      have hyZ : y ∈ Z := by
        refine mem_Z_of_comm_R₀ hs hxL hxN hy fun e he => ?_
        have h1 := hfix ⟨e, Sec9R0_le_Rt hc hxR he⟩ ((hψR₀ _).mp he)
        have h2 : M₀.π ⁅e, y⁆ = 0 := by
          rw [← hcomm ⟨e, Sec9R0_le_Rt hc hxR he⟩ y hyQ, h1, sub_self]
        exact (M₀.π_ker _ (hcQ ⟨e, Sec9R0_le_Rt hc hxR he⟩ y hyQ)).mp h2
      exact (M₀.π_ker y hyQ).mpr hyZ
  set LB' := (LB M Q B).subgroupOf (Rt M (LB M Q B) t) with hLB'
  set LA' := (LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t) with hLA'
  have hLp : IsPGroup 2 ↥(LB M Q B) := hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hLAp : IsPGroup 2 ↥(LB M Q (conjSubgroup r B)) := hcA.isPGroup_LB h34 hs5.width hs5.n_gt
    (hc.noA2_conj hs5.noA2 hrM) (hs5.gen.conj_of_mem hrM)
  have hLRp : IsPGroup 2 ↥LB' := hLp.of_equiv (Subgroup.subgroupOfEquivOfLe hLR).symm
  have hLARp : IsPGroup 2 ↥LA' := hLAp.of_equiv (Subgroup.subgroupOfEquivOfLe hLAR).symm
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  have hcardB : Nat.card (LB'.map ψ) = Nat.card K * Nat.card K := by
    rw [← Subgroup.relIndex_ker, hψk, Subgroup.relIndex_subgroupOf hLR,
      HS9.relIndex_LB_CN h34 hs, hK, pow_two]
  have hLAeq : LA'.map ψ = (LB'.map ψ).map (MulAut.conj (ψ ⟨r, hrR⟩)).toMonoidHom := by
    have hLAc : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) := hc.LB_conj hrM
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : (a : G) ∈ conjSubgroup r (LB M Q B) := hLAc ▸ Subgroup.mem_subgroupOf.mp ha
      refine ⟨ψ ((⟨r, hrR⟩ : ↥(Rt M (LB M Q B) t))⁻¹ * a * ⟨r, hrR⟩),
        ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩, ?_⟩
      · simpa using mem_conjSubgroup.mp ha'
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
        group
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨⟨r, hrR⟩ * b * (⟨r, hrR⟩ : ↥(Rt M (LB M Q B) t))⁻¹,
        Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · rw [hLAc, mem_conjSubgroup]
        have e1 : ((⟨r, hrR⟩ * b * (⟨r, hrR⟩ : ↥(Rt M (LB M Q B) t))⁻¹ : ↥(Rt M (LB M Q B) t)) :
            G) = r * (b : G) * r⁻¹ := rfl
        rw [e1, show r⁻¹ * (r * (b : G) * r⁻¹) * r = (b : G) by group]
        exact Subgroup.mem_subgroupOf.mp hb
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hcardA : Nat.card (LA'.map ψ) = Nat.card K * Nat.card K := by
    rw [hLAeq, Subgroup.card_map_of_injective (MulAut.conj _).injective, hcardB]
  obtain ⟨-, hU₂c, hprodB⟩ := map_eq_prod_of_card _ hLRp ψ hqpos hcardB
    (fun U hU => card_le_of_isPGroup_statedSL U hU)
  obtain ⟨hU₁'c, -, hprodA⟩ := map_eq_prod_of_card _ hLARp ψ hqpos hcardA
    (fun U hU => card_le_of_isPGroup_statedSL U hU)
  set U₁ := LB'.map ((MonoidHom.fst _ _).comp ψ)
  set U₂ := LB'.map ((MonoidHom.snd _ _).comp ψ)
  set U₁' := LA'.map ((MonoidHom.fst _ _).comp ψ)
  set U₂' := LA'.map ((MonoidHom.snd _ _).comp ψ)
  have hne : ∀ U : Subgroup ↥(StatedSL 2 K), Nat.card U = Nat.card K → U ≠ ⊥ := by
    intro U hU hbot
    rw [hbot, Subgroup.card_bot] at hU
    omega
  have hgen : U₁ ⊔ U₁' = ⊤ := by
    have hsup : LB' ⊔ LA' = ⊤ := by
      rw [hLB', hLA', ← Subgroup.subgroupOf_sup hLR hLAR, ← hr.gen, Subgroup.subgroupOf_self]
    have h1 : (LB' ⊔ LA').map ψ = ⊤ := by rw [hsup, Subgroup.map_top_of_surjective ψ hψs]
    rw [Subgroup.map_sup, hprodB, hprodA] at h1
    refine eq_top_iff.mpr fun s _ => ?_
    have hle : U₁.prod U₂ ⊔ U₁'.prod U₂' ≤ (U₁ ⊔ U₁').prod (U₂ ⊔ U₂') :=
      sup_le (Subgroup.prod_mono le_sup_left le_sup_left)
        (Subgroup.prod_mono le_sup_right le_sup_right)
    have h2 : ((s, 1) : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) ∈ (U₁ ⊔ U₁').prod (U₂ ⊔ U₂') :=
      hle (h1 ▸ Subgroup.mem_top _)
    exact h2.1
  have hcommB : ∀ a ∈ LB', ∀ b ∈ LB', ρ a * ρ b = ρ b * ρ a := by
    have h1 := comm_of_mul_self (L := LB'.map ρ) (fun u hu => by
      obtain ⟨a, ha, rfl⟩ := hu
      rw [← map_mul, hρQ]
      have := hc.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.mp ha)
      simpa [pow_two] using this)
    intro a ha b hb
    exact h1 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hcommA : ∀ a ∈ LA', ∀ b ∈ LA', ρ a * ρ b = ρ b * ρ a := by
    have h1 := comm_of_mul_self (L := LA'.map ρ) (fun u hu => by
      obtain ⟨a, ha, rfl⟩ := hu
      rw [← map_mul, hρQ]
      have := hcA.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.mp ha)
      simpa [pow_two] using this)
    intro a ha b hb
    exact h1 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hNeq : ∀ m ∈ ψ.ker, ∃ a ∈ LB' ⊓ ψ.ker, ∃ b ∈ LA' ⊓ ψ.ker, m = a * b := by
    intro m hm
    obtain ⟨a, ha, b, hb, hab⟩ := hprod m ((hmemN m).mp hm)
    refine ⟨⟨a, hNR ha.2⟩, ⟨Subgroup.mem_subgroupOf.mpr ha.1, (hmemN _).mpr ha.2⟩,
      ⟨b, hNR hb.2⟩, ⟨Subgroup.mem_subgroupOf.mpr hb.1, (hmemN _).mpr hb.2⟩, ?_⟩
    exact Subtype.ext hab
  have hP : AlphaPair ρ ψ LB' LA' U₁ U₂ U₁' U₂' :=
    ⟨hcommB, hcommA, hprodB, hprodA, hNeq, hgen, hne U₂ hU₂c, hne U₁' hU₁'c⟩
  haveI : IsSimpleGroup ↥(StatedSL 2 K) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  refine ⟨fun g hg m hm w hw => ?_, fun m hm hmW => ?_⟩
  · set mR : ↥(Rt M (LB M Q B) t) := ⟨m, hNR hm⟩
    have hmk : mR ∈ ψ.ker := (hmemN mR).mpr hm
    have hgm : g * mR * g⁻¹ ∈ ψ.ker := AlphaData.conj_mem_ker hmk
    have hk : ∀ w' ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)), ρ (g * mR * g⁻¹ * mR⁻¹) w' = w' := by
      intro w' hw'
      have h2 := alpha_mul ρ (hD.NV _ hgm) (hD.NW _ (ψ.ker.inv_mem hmk) w' hw')
      rw [hD.alpha_second hP hg hmk hw', hD.alpha_inv hmk hw', add_neg_cancel] at h2
      exact sub_eq_zero.mp h2
    have := (hfixW (g * mR * g⁻¹ * mR⁻¹)).mp hk w hw
    simpa [mR] using this
  · set mR : ↥(Rt M (LB M Q B) t) := ⟨m, hNR hm⟩
    have hmk : mR ∈ ψ.ker := (hmemN mR).mpr hm
    obtain ⟨a, ha, haW, b, hb, hbW, hab⟩ :=
      hD.alpha_decomp hP hmk ((hfixW mR).mpr hmW)
    refine ⟨a, ⟨Subgroup.mem_subgroupOf.mp ha.1, (hmemN a).mp ha.2⟩, (hfixW a).mp haW,
      b, ⟨Subgroup.mem_subgroupOf.mp hb.1, (hmemN b).mp hb.2⟩, (hfixW b).mp hbW, ?_⟩
    have := congrArg Subtype.val hab
    simpa [mR] using this

end Split92

end CFSG.RankThree.GF2n.Stroth80
