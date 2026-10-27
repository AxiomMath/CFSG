module

public import CFSG.Quasithin.Background.Sp4InfMainOne
public import CFSG.Quasithin.Background.FFC11B
public import CFSG.Quasithin.Background.GoldschmidtB69DeepSwap
public import CFSG.Quasithin.Background.GoldschmidtB69DeepNat

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.PairG
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open B6

namespace B69

structure SpTwist {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) (W₁ : Subgroup V)
    (K : Type) [Field K] [Finite K] [CharP K 2] where
  r : ↥L →* ↥(StatedSp 2 K)
  e₁ : Sec W₁ (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K
  he₁ : ∀ (hLW : L ≤ stabSub W₁) (hLU : L ≤ stabSub (fixV L)) (l : ↥L) (s : Sec W₁ (fixV L)),
    e₁ (B5.secHom L hLW hLU l s) = matAut ((r l : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s)
  t : MulAut V
  ht : ∀ x ∈ L, t * x * t⁻¹ ∈ L
  ht' : ∀ x ∈ L, t⁻¹ * x * t ∈ L
  htw : ∃ (A' : GL (Fin 2 ⊕ Fin 2) K) (σ : K ≃+* K), ∀ l l' : ↥L,
    (l' : MulAut V) = t * l * t⁻¹ →
      (((r l' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
          (((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  hniso : ∀ Φ : StdMod (Fin 2 ⊕ Fin 2) K ≃* StdMod (Fin 2 ⊕ Fin 2) K,
    (∀ (l : ↥L) (x : StdMod (Fin 2 ⊕ Fin 2) K),
      Φ (matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) x) =
        matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (Φ x)) → False
  hnorm : ∀ x : MulAut (PairMod (Fin 2 ⊕ Fin 2) K), x ∈ pairSub (Fin 2 ⊕ Fin 2) K →
    (∀ γ ∈ r.range, ∃ δ ∈ r.range,
      x * pairHom (StatedSp 2 K) tauSp γ * x⁻¹ = pairHom (StatedSp 2 K) tauSp δ) →
    (∀ γ ∈ r.range, ∃ δ ∈ r.range,
      x⁻¹ * pairHom (StatedSp 2 K) tauSp γ * x = pairHom (StatedSp 2 K) tauSp δ) →
    x ∈ Sp4.pairNormSp K

theorem exists_twist_data_a6
    {V : Type} [CommGroup V] [Finite V] {X T M L : Subgroup (MulAut V)}
    (hmp : MinParabolic X T M) (hL : CFSG.Open.IsComponentOf L X) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    {H : Subgroup (MulAut (Sec W (W ⊓ fixV L)))} (hLH : autSec L W (W ⊓ fixV L) ≤ H)
    (hn : BinaryNaturalSp4 H ⊤ ⊥ 1)
    (hnormH : ((autSec L W (W ⊓ fixV L)).subgroupOf H).Normal) :
    Nonempty (SpTwist L W (ZMod 2)) := by
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  obtain ⟨K, hKf, hKfin, hK, r, -, hrn, hrne, e₁, he₁⟩ := natural_data_sp4_gen hW hLH hn
  have hrnorm : r.range.Normal := hrn hnormH
  have hrne' : r.range ≠ ⊥ := hrne (nontrivial_autSec hW)
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK2]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  let r' : ↥L →* StatedSp 2 (ZMod 2) := (Sp4Inf.mapSp e).toMonoidHom.comp r
  let e₁' := e₁.trans (Sp4Inf.stdMapEquiv e)
  have he₁' : ∀ (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub (fixV L))
      (l : ↥L) (s : Sec W (fixV L)),
      e₁' (B5.secHom L hLW hLU l s) =
        matAut ((r' l : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (e₁' s) := by
    intro hLW hLU l s
    show Sp4Inf.stdMapEquiv e (e₁ (B5.secHom L hLW hLU l s)) = _
    rw [he₁ hLW hLU l s, Sp4Inf.stdMapEquiv_matAut]
    rfl
  have hrange : r'.range = r.range.map (Sp4Inf.mapSp e).toMonoidHom :=
    MonoidHom.range_comp (Sp4Inf.mapSp e).toMonoidHom r
  have hnormD : r'.range.Normal := by
    rw [hrange]
    exact hrnorm.map _ (Sp4Inf.mapSp e).surjective
  have hneD : r'.range ≠ ⊥ := by
    rw [hrange]
    intro h
    exact hrne' ((Subgroup.map_eq_bot_iff_of_injective (f := (Sp4Inf.mapSp e).toMonoidHom) r.range
      (Sp4Inf.mapSp e).injective).1 h)
  have hLperf : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have hperfD : Group.IsPerfect ↥(r'.range) := Group.IsPerfect.range r'
  have hDalt : Sp4Inf.IsAlt6Sub r'.range := Sp4Inf.isAlt6Sub_of_perfect_normal hperfD hnormD hneD
  have hDalt' : r'.range.map Sp4Inf.iotaSp.toMonoidHom = alternatingGroup (Fin 6) := hDalt
  have hmemA : ∀ l : ↥L, Sp4Inf.iotaSp (r' l) ∈ alternatingGroup (Fin 6) := fun l => by
    have h1 : Sp4Inf.iotaSp (r' l) ∈ r'.range.map Sp4Inf.iotaSp.toMonoidHom :=
      ⟨r' l, ⟨l, rfl⟩, rfl⟩
    rwa [hDalt'] at h1
  let π₀ : ↥L →* ↥(alternatingGroup (Fin 6)) :=
    (Sp4Inf.iotaSp.toMonoidHom.comp r').codRestrict (alternatingGroup (Fin 6)) hmemA
  have hπ₀ : Function.Surjective π₀ := by
    intro y
    have : (y : Equiv.Perm (Fin 6)) ∈ r'.range.map Sp4Inf.iotaSp.toMonoidHom := by
      rw [hDalt']
      exact y.2
    obtain ⟨x, ⟨l, rfl⟩, hx⟩ := this
    exact ⟨l, Subtype.ext hx⟩
  have hcenter : Subgroup.center ↥(alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hev : Even (Nat.card ↥(alternatingGroup (Fin 6))) := by
    rw [Sp4Inf.card_alt_six']
    exact ⟨180, by norm_num⟩
  obtain ⟨t, ht, ht', thb, hthb, hnot⟩ :=
    exists_twist_element hmp hL Sp4Inf.swapGeo_alt6 hev hcenter π₀ hπ₀
  obtain ⟨γ₁, hγ₁⟩ := (Sp4Inf.ext_alt6 thb).resolve_left hnot
  have htw : ∃ (A' : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (σ : ZMod 2 ≃+* ZMod 2), ∀ l l' : ↥L,
      (l' : MulAut V) = t * l * t⁻¹ →
        (((r' l' : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
          (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *
            (((tauSp (r' l) : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map σ *
            (((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod 2))) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
    refine ⟨(γ₁ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)), RingEquiv.refl _, fun l l' hl' => ?_⟩
    have h1 := hγ₁ (π₀ l)
    have h2 : thb (π₀ l) = π₀ l' := hthb l l' hl'
    rw [h2] at h1
    have h3 : Sp4Inf.iotaSp (r' l') = Sp4Inf.iotaSp (γ₁ * tauSp (r' l) * γ₁⁻¹) := by
      have h1' : Sp4Inf.iotaSp (r' l') = Sp4Inf.iotaSp
          (γ₁ * tauSp (Sp4Inf.iotaSp.symm (Sp4Inf.iotaSp (r' l))) * γ₁⁻¹) := h1
      rwa [MulEquiv.symm_apply_apply] at h1'
    have h4 : (r' l' : StatedSp 2 (ZMod 2)) = γ₁ * tauSp (r' l) * γ₁⁻¹ :=
      Sp4Inf.iotaSp.injective h3
    rw [h4, Sp4Inf.matrix_map_refl]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  have hniso : ∀ Φ : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) ≃* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2),
      (∀ (l : ↥L) (x : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2)),
        Φ (matAut ((r' l : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) x) =
          matAut ((tauSp (r' l) : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (Φ x)) →
        False := by
    intro Φ hΦ
    refine Sp4Inf.no_tau_iso hDalt Φ (fun γ hγ x => ?_)
    obtain ⟨l, rfl⟩ := hγ
    exact hΦ l x
  exact ⟨⟨r', e₁', he₁', t, ht, ht', htw, hniso, fun x hx h₁ h₂ =>
    Sp4Inf.mem_pairNormSp_of_normalizes hDalt hx h₁ h₂⟩⟩

end B69

end CFSG.Quasithin
