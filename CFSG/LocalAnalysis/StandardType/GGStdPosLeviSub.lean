module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLeviTorus
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosCore
public import CFSG.LocalAnalysis.StandardType.GGStdPosTrans
public import CFSG.LocalAnalysis.StandardType.GGStdPosTorusNorm
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem ggStdPosLevi_pow_mem {K : Type*} [Group K] {T L : Subgroup K}
    (hTL : T ≤ Subgroup.normalizer (L : Set K)) {N : ℕ} (hT : ∀ t ∈ T, t ^ N = 1) {κ : K}
    (hκ : κ ∈ T ⊔ L) : κ ^ N ∈ L := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T L hTL, Set.mem_mul] at hκ
  obtain ⟨t, ht, l, hl, rfl⟩ := hκ
  have key : ∀ j : ℕ, ∃ l' ∈ L, (t * l) ^ j = t ^ j * l' := by
    intro j
    induction j with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨l', hl', e⟩ := ih
      refine ⟨t⁻¹ * l' * t * l, L.mul_mem ?_ hl, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem ht)) l').mp hl'
        rwa [inv_inv] at h1
      · rw [pow_succ, e, pow_succ]
        group
  obtain ⟨l', hl', e⟩ := key N
  rwa [e, hT t ht, one_mul]

theorem ggStdPosLevi_mem_map {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {k : Type*} [Field k] [Finite k]
    [CharP k 2] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D k x C O)
    (hdiv : D.divisible = ∅) {s : kˣ} (hs : s ≠ 1) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ} {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {ν : GGWeyl D →* K} (hν : GGWeylLift D ν) (w : GGWeyl D) (i : Fin D.rank)
    (hR1 : ∀ β ∈ D.roots, D.rootGroup β ≤ Subgroup.centralizer
        (ggTorusRootKer D p (weylAction D.isFiniteType w (Pi.single i 1))) →
      β = weylAction D.isFiniteType w (Pi.single i 1) ∨
        β = -weylAction D.isFiniteType w (Pi.single i 1))
    (hR2 : ∀ w' : GGWeyl D,
      (∀ h ∈ ggTorusRootKer D p (weylAction D.isFiniteType w (Pi.single i 1)),
        ν w' * h * (ν w')⁻¹ * h⁻¹ ∈ Subgroup.center K) →
      w' = 1 ∨ w' = w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)
    {S : Set G} (hS : ∀ b, b ∈ S ↔ b ∈ Bs ∧
      b * ψ (ν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)) =
        ψ (ν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)) * b)
    {y : G} (hy : y ∈ ψ.range) (hyS : y ∈ Subgroup.centralizer S) {e : ℕ}
    (he : y ^ 2 ^ e = 1) :
    y ∈ (D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) ⊔
      D.rootGroup (-weylAction D.isFiniteType w (Pi.single i 1))).map ψ := by
  have hγ : weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots :=
    weylAction_mem_roots (single_mem_roots i) w
  have hmL : ν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹) ∈
      D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) ⊔
        D.rootGroup (-weylAction D.isFiniteType w (Pi.single i 1)) := by
    have hact := ggStdPos_actsAs_weylLift hν w
    have h2 := hact _ (neg_single_mem_roots i)
    rw [map_neg] at h2
    rw [← hact _ (single_mem_roots i), ← h2, ← Subgroup.map_sup, map_mul, map_mul, map_inv]
    exact ⟨_, hν.simple_mem i, rfl⟩
  generalize weylAction D.isFiniteType w (Pi.single i 1) = γ at hγ hmL hR1 hR2 ⊢
  generalize w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹ = w' at hmL hR2 hS
  have hγ' : -γ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hγ
  have hpar := (hE.param γ hγ).1
  have hTab : ∀ a ∈ ggTorus D, ∀ c ∈ ggTorus D, a * c = c * a := by
    intro a ha c hc
    rw [ggStdPos_ggTorus_eq hct hext hBU] at ha hc
    exact Subgroup.mem_centralizer_iff.mp
      (LieType.TitsSimplicity.iSup_le_centralizer_iSup hext hc) a ha
  have hcen : ∀ a b : K, ψ a * ψ b = ψ b * ψ a → a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center K :=
    fun a b hab => hker (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hab,
        mul_inv_cancel_right, mul_inv_cancel])
  have hEL : ∀ h ∈ ggTorusRootKer D p γ,
      D.rootGroup γ ⊔ D.rootGroup (-γ) ≤ Subgroup.centralizer {h} := by
    rintro h ⟨hhT, -, hhc⟩
    obtain ⟨μ, hμ, hμ'⟩ := ggStdPosLevi_conj_scalar hct hext hBU hE hhT hγ
    have h1 : (μ : k) = 1 := by
      have e1 := Subgroup.mem_centralizer_singleton_iff.mp (hhc ((hpar _).mpr ⟨1, rfl⟩))
      have e2 : x γ ((μ : k) * 1) = x γ 1 := by rw [← hμ, ← e1, mul_inv_cancel_right]
      have e3 := (hE.param γ hγ).2.2 e2
      rwa [mul_one] at e3
    refine sup_le hhc fun z hz => ?_
    obtain ⟨c, rfl⟩ := ((hE.param (-γ) hγ').1 z).mp hz
    have e4 := hμ' c
    rw [Units.val_inv_eq_inv_val, h1, inv_one, one_mul] at e4
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp e4).symm
  have hES : ∀ h ∈ ggTorusRootKer D p γ, ψ h ∈ S := by
    intro h hh
    refine (hS _).mpr ⟨hC3 _ (ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hBs h hh.1)
      (by rw [← map_pow, hh.2.1, map_one]), ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hEL h hh hmL)]
  have hZ : ∀ β ∈ D.roots, ∀ z ∈ D.rootGroup β, z ∈ Subgroup.center K → z = 1 := by
    intro β hβ z hz hzc
    obtain ⟨t, -, ht⟩ := ggStdPos_exists_fixFree hct hext hBU hE hdiv hs β hβ
    exact ht z hz (by rw [Subgroup.mem_center_iff.mp hzc t, mul_inv_cancel_right])
  have hQ : (Subgroup.centralizer S).comap ψ ≤ ggTorus D ⊔ (D.rootGroup γ ⊔ D.rootGroup (-γ)) := by
    rw [ggStdPos_centralizer_eq hct hext hBU (ggStdPos_transitive_of_chevalleyExtras hct hE hdiv)
      ψ hker S fun b hb => hBs b ((hS b).mp hb).1]
    refine sup_le (fun κ hκ => ?_) (iSup₂_le fun β hβ => ?_)
    · obtain ⟨h₀, hh₀, w'', rfl⟩ :=
        (ggStdPos_mem_normalizer_ggTorus_iff hct hext hBU hE hdiv hs hν κ).mp hκ.2
      refine (hR2 w'' fun h' hh' => ?_).elim (fun h1 => ?_) fun h1 => ?_
      · have hA : ν w'' * h' * (ν w'')⁻¹ ∈ ggTorus D :=
          ggStdPos_conj_mem_ggTorus_of_actsAs hh'.1 (ggStdPos_actsAs_weylLift hν w'')
        have e1 : h₀ * ν w'' * h' * (h₀ * ν w'')⁻¹ * h'⁻¹ = ν w'' * h' * (ν w'')⁻¹ * h'⁻¹ := by
          calc h₀ * ν w'' * h' * (h₀ * ν w'')⁻¹ * h'⁻¹ =
                h₀ * (ν w'' * h' * (ν w'')⁻¹) * h₀⁻¹ * h'⁻¹ := by group
            _ = _ := by rw [hTab _ hh₀ _ hA, mul_inv_cancel_right]
        exact e1 ▸ hcen _ h' (Subgroup.mem_centralizer_iff.mp hκ.1 _ (hES h' hh')).symm
      · rw [h1, map_one, mul_one]
        exact Subgroup.mem_sup_left hh₀
      · rw [h1]
        exact Subgroup.mul_mem_sup hh₀ hmL
    · refine (hR1 β hβ.1 fun z hz => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_).elim
        (fun h1 => h1 ▸ le_sup_of_le_right le_sup_left)
        fun h1 => h1 ▸ le_sup_of_le_right le_sup_right
      have hzh : h * z⁻¹ * h⁻¹ ∈ D.rootGroup β := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh.1 β) hβ.1) _).mp (inv_mem hz)
      have h1 := hZ β hβ.1 _ (mul_mem hz hzh) (by
        simpa only [mul_assoc] using
          hcen z h (Subgroup.mem_centralizer_iff.mp (hβ.2 hz) _ (hES h hh)).symm)
      calc h * z = (z * (h * z⁻¹ * h⁻¹))⁻¹ * z * h := by group
        _ = z * h := by rw [h1, inv_one, one_mul]
  have hTL : ggTorus D ≤
      Subgroup.normalizer ((D.rootGroup γ ⊔ D.rootGroup (-γ) : Subgroup K) : Set K) := by
    intro h hh
    have hN : ∀ β ∈ D.roots, (D.rootGroup β).map (MulAut.conj h).toMonoidHom = D.rootGroup β :=
      fun β hβ => CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp
        (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh β) hβ)
    rw [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj, Subgroup.map_sup, hN γ hγ,
      hN (-γ) hγ']
  have hodd : Odd (Nat.card kˣ) := by
    haveI := Fintype.ofFinite k
    obtain ⟨f, -, hf⟩ := FiniteField.card k 2
    have h1 : 2 ∣ 2 ^ (f : ℕ) := dvd_pow_self 2 f.pos.ne'
    have h2 : 0 < 2 ^ (f : ℕ) := by positivity
    rw [Nat.card_units, Nat.card_eq_fintype_card, hf, Nat.odd_iff]
    omega
  obtain ⟨κ, rfl⟩ := MonoidHom.mem_range.mp hy
  have hN : ψ κ ^ Nat.card kˣ ∈ (D.rootGroup γ ⊔ D.rootGroup (-γ)).map ψ := by
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem ψ (ggStdPosLevi_pow_mem hTL
      (fun t ht => ggStdPosLevi_pow_card hct hext hBU hE ht) (hQ hyS))
  exact Subgroup.zpowers_le.mpr hN (mem_zpowers_pow_iff.mpr
    ((Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hodd)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one he)))

end CFSG.StandardType

end
