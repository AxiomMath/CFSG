module

public import CFSG.Quasithin.Vol2.Ch11SecC37B5
public import CFSG.Quasithin.Vol2.Ch11SecDSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem d0Of_le_normalizer_V₁ (i : Inp37) (hJ : L = ⁅L, thompsonJ T⁆) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G)))
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    d0Of D ≤ Subgroup.normalizer (V₁ : Set G) := by
  rw [s.V₁_eq_inf i hVL]
  intro d hd
  have hdL : d ∈ L := d0Of_le i.h1104 i.h1134 i.h1135 i.h1136 i.hB s.hyp hJ s.hV₁ s.h31 s.hnot
    s.hAT s.hAC hD hd
  exact F7.mem_normalizer_inf (SecA.L_le_normalizer_fsuV s.hyp hdL)
    (le_normalizer_centralizer (s.d0Of_le_normalizer i.h1102 i.h1104 i.h1134 i.h1135 i.h1136
      i.hB i.hBS i.hBP hJ hD) hd)

theorem V₁_eq_commutator (i : Inp37) (hJ : L = ⁅L, thompsonJ T⁆) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    V₁ = ⁅V₁, d0Of D⁆ := by
  have hVL := s.fsuV_inf_centralizer_L hJ i.hG16 i.hAS i.hFPF i.hF i.h1102 i.hKF.2.2.2 i.h1122
    i.h1104 i.h1134 i.h1135 i.h1136 i.h331 i.hSN i.hB hD
  have hN := s.d0Of_le_normalizer_V₁ i hJ hD hVL
  obtain ⟨d, hd, hfpf⟩ := s.exists_fpf i hJ hD
  have hTV₁ := s.inf_le_centralizer_V₁ i.hFC1 i.h1102
  have hVU := s.fsuV_le_U i.h1102 hVL
  have hfix : ∀ v ∈ V₁, d * v * d⁻¹ = v → v = 1 := by
    intro v hv hdv
    have hvV := SecA.IsVi.le_fsuV s.hV₁ hv
    have hvL := hfpf v (hVU hvV) (fun p hp => by
      rw [← Subgroup.mem_centralizer_iff.mp (hTV₁ hp) v hv, mul_inv_cancel_right]) hdv
    have : v ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨hvV, hvL⟩
    rwa [hVL, Subgroup.mem_bot] at this
  have hdN := hN hd
  refine le_antisymm (fun v hv => ?_) ?_
  · let f : ↥V₁ → ↥V₁ := fun w => ⟨w * d * (w : G)⁻¹ * d⁻¹, by
      rw [mul_assoc, mul_assoc, ← mul_assoc d]
      exact V₁.mul_mem w.2 ((Subgroup.mem_normalizer_iff.mp hdN _).mp (V₁.inv_mem w.2))⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (a : G) * d * (a : G)⁻¹ * d⁻¹ = b * d * (b : G)⁻¹ * d⁻¹ :=
        congrArg Subtype.val hab
      have h2 : d * ((b : G)⁻¹ * a) * d⁻¹ = (b : G)⁻¹ * a := by
        calc d * ((b : G)⁻¹ * a) * d⁻¹ =
              (b : G)⁻¹ * (b * d * (b : G)⁻¹ * d⁻¹) * (d * a * d⁻¹) := by group
          _ = (b : G)⁻¹ * a := by rw [← h1]; group
      exact Subtype.ext (inv_mul_eq_one.mp (hfix _ (V₁.mul_mem (V₁.inv_mem b.2) a.2) h2)).symm
    obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hf) ⟨v, hv⟩
    have hv' : v = ⁅(w : G), d⁆ := by
      rw [commutatorElement_def]
      exact (congrArg Subtype.val hw).symm
    rw [hv']
    exact Subgroup.commutator_mem_commutator w.2 hd
  · rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc x]
    exact V₁.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hN hx) _).mp (V₁.inv_mem hv))

omit [Finite G] s in
theorem mem_normalizer_TL (hOT : pCoreOf 2 (L ⊔ T) ≤ T) {d : G} (hdL : d ∈ L)
    (hdN : d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) :
    d ∈ Subgroup.normalizer (TL T L : Set G) := by
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  have key : ∀ y ∈ L, y ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) →
      ∀ x ∈ TL T L, y * x * y⁻¹ ∈ TL T L := by
    intro y hyL hyN x hx
    have hx2 : x ∈ pCoreOf 2 (L ⊔ T) ⊔ L := by
      rw [sup_comm]
      exact hx.2
    obtain ⟨o, ho, l, hl, hxol⟩ := mem_sup_of_le_normalizer hLO hx2
    have hlT : l ∈ T := by
      have : l = o⁻¹ * x := by rw [hxol]; group
      rw [this]
      exact T.mul_mem (T.inv_mem (hOT ho)) hx.1
    have h1 : y * o * y⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hLO hyL) o).mp ho
    have h2 : y * l * y⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hyN l).mp ⟨hlT, hl⟩
    have e : y * x * y⁻¹ = (y * o * y⁻¹) * (y * l * y⁻¹) := by rw [hxol]; group
    rw [e]
    exact ⟨T.mul_mem (hOT h1) h2.1,
      Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2.2)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key d hdL hdN x, fun hx => ?_⟩
  have := key d⁻¹ (L.inv_mem hdL) (Subgroup.inv_mem _ hdN) _ hx
  simpa [mul_assoc] using this

theorem exists_isCartanX_d0Of (i : Inp37) (hJ : L = ⁅L, thompsonJ T⁆) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    ∃ X : Subgroup G, IsCartanX T L X ∧ d0Of D ≤ X := by
  obtain ⟨X₀, hX₀⟩ := SecD.exists_isCartanX s.hyp
  have hTLN : T ⊓ L ≤ L ⊓ Subgroup.normalizer (TL T L : Set G) :=
    le_inf inf_le_right fun x hx => Subgroup.le_normalizer (SecD.inf_L_le_TL T L hx)
  have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ L) (L ⊓ Subgroup.normalizer (TL T L : Set G)) :=
    A4.isSylowTwoOf_mono s.sylow_TL hTLN inf_le_left
  have hnorm : L ⊓ Subgroup.normalizer (TL T L : Set G) ≤
      Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    intro x hx
    rw [← SecD.TL_inf_L T L]
    exact F7.mem_normalizer_inf hx.2 (Subgroup.le_normalizer hx.1)
  have hdN := s.d0Of_le_normalizer i.h1102 i.h1104 i.h1134 i.h1135 i.h1136 i.hB i.hBS i.hBP hJ hD
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := F7.isSylowTwoOf_pCoreOf_le s.sylow_LT
  have hD₀Y : d0Of D ≤ L ⊓ Subgroup.normalizer (TL T L : Set G) := fun d hd => by
    have hdL : d ∈ L := d0Of_le i.h1104 i.h1134 i.h1135 i.h1136 i.hB s.hyp hJ s.hV₁ s.h31
      s.hnot s.hAT s.hAC hD hd
    exact ⟨hdL, mem_normalizer_TL hOT hdL (hdN hd)⟩
  have hodd : Odd (Nat.card (d0Of D)) :=
    hD.2.1.of_dvd_nat (Subgroup.card_dvd_of_le (d0Of_le_self D))
  obtain ⟨p, hp, hle⟩ := exists_conj_le_of_normal_sylow hsyl hnorm hX₀ hD₀Y hodd
  exact ⟨X₀.map (MulAut.conj p).toMonoidHom, isHallTwoPrimeOf_conj hX₀ (hsyl.1 hp), hle⟩

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
