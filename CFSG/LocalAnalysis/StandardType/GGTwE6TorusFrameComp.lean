module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H]
    (β : G →* H) (hβ : Function.Injective β) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map β =
      β.range ⊓ Subgroup.centralizer ({β x} : Set H) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨y, rfl⟩, ?_⟩
    have hy' : y ∈ Subgroup.centralizer ({x} : Set G) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, hy']
  · rintro ⟨⟨y, rfl⟩, hz⟩
    refine ⟨y, ?_, rfl⟩
    have hz' : β y ∈ Subgroup.centralizer ({β x} : Set H) := hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz'
    change y ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hβ
    rw [map_mul, map_mul]
    exact hz'

private noncomputable def corootTupleHom {L : Type} [Field L]
    (α : Fin Tag.E6.rank → ℤ) :
    Lˣ →* (Fin Tag.E6.rank → Lˣ) where
  toFun := fun s => CFSG.SeitzReduction.E6Pilot.corootTuple α s
  map_one' := CFSG.SeitzReduction.E6Pilot.corootTuple_one α
  map_mul' := CFSG.SeitzReduction.E6Pilot.corootTuple_mul α

private theorem corootTupleE_pow {L : Type} [Field L]
    (α : Fin Tag.E6.rank → ℤ) (s : Lˣ) (n : ℕ) :
    CFSG.SeitzReduction.E6Pilot.corootTuple α (s ^ n) =
      CFSG.SeitzReduction.E6Pilot.corootTuple α s ^ n := by
  exact map_pow (corootTupleHom (L := L) α) s n

private theorem rootDiagUnit_corootTupleE_pow {L : Type} [Field L]
    (α : Fin Tag.E6.rank → ℤ) (s : Lˣ) (n : ℕ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6
        (CFSG.SeitzReduction.E6Pilot.corootTuple α (s ^ n)) =
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6
        (CFSG.SeitzReduction.E6Pilot.corootTuple α s)) ^ n := by
  rw [corootTupleE_pow, CFSG.LieType.Chevalley.rootDiagUnit_pow]

private theorem orderOf_rootDiagUnit_corootTupleE {L : Type} [Field L] [IsAlgClosed L]
    {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) {s : Lˣ}
    (hs : orderOf s = p ^ e) :
    orderOf (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6
      (CFSG.SeitzReduction.E6Pilot.corootTuple α s)) = p ^ e := by
  set x := CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6
    (CFSG.SeitzReduction.E6Pilot.corootTuple α s) with hx
  have hdvd : orderOf x ∣ p ^ e := by
    rw [orderOf_dvd_iff_pow_eq_one, hx]
    rw [← rootDiagUnit_corootTupleE_pow (L := L) (α := α) s (p ^ e), ← hs,
      pow_orderOf_eq_one]
    have h1t : CFSG.SeitzReduction.E6Pilot.corootTuple α (1 : Lˣ) = 1 :=
      CFSG.SeitzReduction.E6Pilot.corootTuple_one α
    rw [h1t, CFSG.LieType.Chevalley.rootDiagUnit_one]
  have hdvd' : p ^ e ∣ orderOf x := by
    have htuple : CFSG.SeitzReduction.E6Pilot.corootTuple α (s ^ orderOf x) = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L)
      rw [rootDiagUnit_corootTupleE_pow (L := L) (α := α) s (orderOf x), ← hx,
        pow_orderOf_eq_one, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have hchar : (s ^ orderOf x) ^ 2 = 1 := by
      have h := congrArg
        (fun a => CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a α) htuple
      have hrc := CFSG.SeitzReduction.E6Pilot.rootChar_corootTuple
        (δ := α) (c := s ^ orderOf x) α
      have hif : CFSG.LieType.Steinberg.Adjoint.iform α α = 2 :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E6 hα
      have hrc' : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar
          (CFSG.SeitzReduction.E6Pilot.corootTuple α (s ^ orderOf x)) α =
          (s ^ orderOf x) ^ 2 :=
        hrc.trans (congrArg (fun e => (s ^ orderOf x) ^ e) hif)
      have h2 : (s ^ orderOf x) ^ 2 =
          CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar 1 α :=
        hrc'.symm.trans h
      simpa [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar] using h2
    have hdvd_s : orderOf s ∣ orderOf x * 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
      exact hchar
    rw [hs] at hdvd_s
    have hcop2 : Nat.Coprime p 2 := by
      rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
      exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h)
    exact (hcop2.pow_left e).dvd_of_dvd_mul_right hdvd_s
  exact Nat.dvd_antisymm hdvd hdvd'

theorem exists_fullOrder_of_component
    {f p e : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hpe : p ^ e ∣ 2 ^ f + 1)
    (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L 2] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    {ζK : Kˣ} {hζ : (Units.map (algebraMap K L).toMonoidHom ζK) ^ p = 1}
    {g₀ : ModGL TwistTag.E6.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (hlang : twistHom TwistTag.E6 L Fr g₀ =
      g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl)
    (T : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hbase : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K L)
        ((ι₀ (Multiplicative.ofAdd s) : _) : ModGL TwistTag.E6.tag K) =
        g₀ * frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ s *
          g₀⁻¹)
    (hcent : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ x ∈ ι₀.range, c * x = x * c) → c ∈ T)
    {x : ↥(graphFixedRootGroup TwistTag.E6 K σ)} (hx : x ∈ ι₀.range) (hx1 : x ≠ 1)
    {J : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    (hJ : IsComponentOf J (Subgroup.centralizer {x})) :
    ∃ y ∈ J, y ∈ T ∧ orderOf y = p ^ e := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨s, hs⟩ : ∃ s : Fin TwistTag.E6.tag.rank → ZMod p,
      x = ι₀ (Multiplicative.ofAdd s) := by
    obtain ⟨s, hs⟩ := hx
    exact ⟨Multiplicative.toAdd s, by simpa using hs.symm⟩
  let ζ : Lˣ := Units.map (algebraMap K L).toMonoidHom ζK
  have hζ' : ζ ^ p = 1 := hζ
  let a : Fin TwistTag.E6.tag.rank → Lˣ :=
    TableBExc.E6Three.zetaVec ζ hζ' (frameCoord TwistTag.E6.tag p s)
  have hbase' : ∀ t : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K L)
        ((ι₀ (Multiplicative.ofAdd t) : _) : ModGL TwistTag.E6.tag K) =
        g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ' t * g₀⁻¹ := by
    intro t
    simpa [ζ] using hbase t
  let β : (↥(graphFixedRootGroup TwistTag.E6 K σ)) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (graphFixedRootGroup TwistTag.E6 K σ).subtype
  have hβinj : Function.Injective β := by
    change Function.Injective ((baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K σ).subtype)
    exact (baseChangeGL_injective (algebraMap K L)).comp
      (Subgroup.subtype_injective (graphFixedRootGroup TwistTag.E6 K σ))
  have hβapply : ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      β z = baseChangeGL (algebraMap K L) ((z : _) : ModGL TwistTag.E6.tag K) := fun _ => rfl
  have hβx : β x = g₀ * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a * g₀⁻¹ := by
    rw [hs]
    exact hbase' s
  have h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a ≠ 1 := by
    intro ha1
    apply hx1
    apply hβinj
    calc β x = g₀ * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a * g₀⁻¹ := hβx
      _ = g₀ * 1 * g₀⁻¹ := by rw [ha1]
      _ = β 1 := by rw [map_one]; group
  have hap : ∀ k, a k ^ p = 1 := by
    intro k
    change (TableBExc.E6Three.zetaVec ζ hζ' (frameCoord TwistTag.E6.tag p s) k) ^ p = 1
    rw [TableBExc.E6Three.zetaVec_apply]
    rw [show (ζ ^ ((frameCoord TwistTag.E6.tag p s k).val) : Lˣ) =
        ζ ^ (((frameCoord TwistTag.E6.tag p s k).val) : ℤ) from
        (zpow_natCast ζ _).symm]
    exact TwE6RootKill.zpow_pow_eq_one_rk hζ' _
  have haq : ∀ k, a k ^ (2 ^ f + 1) = 1 := by
    intro k
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hap k, one_pow]
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hq2 : Even (2 ^ f) :=
    even_iff_two_dvd.2 (dvd_pow_self 2 (by omega : f ≠ 0))
  have hqpow : IsPrimePow (2 ^ f) :=
    (isPrimePow_pow_iff (n := 2) (k := f) (by omega : f ≠ 0)).2
      (Nat.Prime.isPrimePow Nat.prime_two)
  have hW : twE6PhiTwoWeyl =
      CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0 := rfl
  have hg : twistHom TwistTag.E6 L Fr g₀ =
      g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L
        CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0 := by
    rw [← hW]
    exact hlang
  obtain ⟨hfinR, -, hder, -, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf K hK σ hσ L Fr hFr
  have hfinF : Finite (fixModel (τ := TwistTag.E6.tag) (twistHom TwistTag.E6 L Fr)) := hfinR
  have hfix : fixModel (τ := TwistTag.E6.tag) (twistHom TwistTag.E6 L Fr) =
      twistedFixedGroup TwistTag.E6 L Fr := rfl
  have hn : ∀ k, g₀ * weylElt TwistTag.E6.tag L k 1 * g₀⁻¹ ∈
      ⁅fixModel (τ := TwistTag.E6.tag) (twistHom TwistTag.E6 L Fr),
        fixModel (τ := TwistTag.E6.tag) (twistHom TwistTag.E6 L Fr)⁆ := by
    obtain ⟨m, hm, -⟩ := exists_langFrame_weyl (f := f) (p := p) hf K hK σ hσ L Fr hFr
      (ζ := ζ) hζ' hg₀C hg ι₀ hbase'
    intro k
    have hmk := hm ((coxeterSystem TwistTag.E6.tag).simple k)
    rw [CFSG.LieType.Chevalley.canonicalRep_simple (coxeterSystem TwistTag.E6.tag) L k] at hmk
    have hmem : baseChangeGL (algebraMap K L)
        (((m ((coxeterSystem TwistTag.E6.tag).simple k) : _) :
          ModGL TwistTag.E6.tag K)) ∈
        (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)) :=
      ⟨_, (m ((coxeterSystem TwistTag.E6.tag).simple k)).2, rfl⟩
    rw [hmk] at hmem
    rw [← hder] at hmem
    rw [hfix]
    exact hmem
  have hcomp : CFSG.Assembly.IsComponentOf (J.map β)
      (β.range ⊓ Subgroup.centralizer {β x}) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ β hβinj
    rwa [map_centralizer_singleton β hβinj x] at h
  have hβrange : β.range =
      (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hK' : CFSG.Open.IsComponentOf (J.map β)
      (⁅fixModel (τ := TwistTag.E6.tag) (twistHom TwistTag.E6 L Fr),
        fixModel (τ := TwistTag.E6.tag) (twistHom TwistTag.E6 L Fr)⁆ ⊓
        Subgroup.centralizer {g₀ * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a * g₀⁻¹}) := by
    apply CFSG.Assembly.isComponentOf_iff_open.1
    have h := hcomp
    rw [hβrange] at h
    have hcomm : ⁅fixModel (τ := TwistTag.E6.tag) (twistHom TwistTag.E6 L Fr),
        fixModel (τ := TwistTag.E6.tag) (twistHom TwistTag.E6 L Fr)⁆ =
        (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)) := by
      rw [hfix, hder]
    rw [hcomm]
    rwa [← hβx]
  obtain ⟨α, hα, -, hc⟩ := CFSG.StandardType.TwE6Coroot.exists_corootTorus_le_frame
      (L := L) (Fr := Fr) (q := 2 ^ f) hq0 hq2 hFr hqpow hfinF hg₀C hg hn
      (Fact.out : p.Prime) (by omega : p ≠ 2) hap haq h1 hK'
  have hp_dvd : p ^ e ∣ Nat.card K - 1 := by
    rw [hK]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ f) 1
    rw [hsq]
    exact dvd_mul_of_dvd_right hpe (2 ^ f - 1)
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (by norm_num))
  obtain ⟨ζ₀, hζ₀ord⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.exists_orderOf_eq_of_dvd_card_sub_one
      (F := K) hp_dvd
  let s₀ : Lˣ := Units.map (algebraMap K L).toMonoidHom ζ₀
  have hmapinj : Function.Injective (Units.map (algebraMap K L).toMonoidHom) := by
    intro u v h
    exact Units.ext ((algebraMap K L).injective (congrArg (fun w : Lˣ => (w : L)) h))
  have hs₀ord : orderOf s₀ = p ^ e := by
    rw [show s₀ = Units.map (algebraMap K L).toMonoidHom ζ₀ from rfl,
      orderOf_injective (Units.map (algebraMap K L).toMonoidHom) hmapinj ζ₀, hζ₀ord]
  have hs₀q : s₀ ^ (2 ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ := hpe
    rw [hm, pow_mul, ← hs₀ord, pow_orderOf_eq_one, one_pow]
  let c : ModGL TwistTag.E6.tag L := CFSG.StandardType.TwE6Coroot.coroot α s₀
  have hc' : g₀ * c * g₀⁻¹ ∈ J.map β := hc s₀ hs₀q
  obtain ⟨y, hyJ, hyβ⟩ := Subgroup.mem_map.mp hc'
  have hyT : y ∈ T := by
    apply hcent
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    apply hβinj
    have hzβ : β (ι₀ t) =
        g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ' (Multiplicative.toAdd t) * g₀⁻¹ := by
      rw [hβapply (ι₀ t)]
      exact hbase' (Multiplicative.toAdd t)
    rw [map_mul, map_mul, hyβ, hzβ]
    have hcT : c ∈ torusGroup TwistTag.E6.tag L := by
      change CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6
        (CFSG.SeitzReduction.E6Pilot.corootTuple α s₀) ∈ torusGroup Tag.E6 L
      exact CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup _
    have hfT : frameDiag (τ := TwistTag.E6.tag) ζ hζ' (Multiplicative.toAdd t) ∈
        torusGroup TwistTag.E6.tag L :=
      CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup
        (TableBExc.E6Three.zetaVec ζ hζ' (frameCoord TwistTag.E6.tag p (Multiplicative.toAdd t)))
    have hcomm := CFSG.RankThree.PartOne.KE.torusGroup_comm hcT hfT
    calc g₀ * c * g₀⁻¹ *
          (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ' (Multiplicative.toAdd t) * g₀⁻¹)
        = g₀ * (c * frameDiag (τ := TwistTag.E6.tag) ζ hζ' (Multiplicative.toAdd t)) * g₀⁻¹ :=
          by group
      _ = g₀ * (frameDiag (τ := TwistTag.E6.tag) ζ hζ' (Multiplicative.toAdd t) * c) * g₀⁻¹ :=
          by rw [hcomm]
      _ = (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ' (Multiplicative.toAdd t) * g₀⁻¹) *
          (g₀ * c * g₀⁻¹) := by group
  have hyord : orderOf y = p ^ e := by
    have hβy : orderOf (β y) = orderOf y := orderOf_injective β hβinj y
    have hconj : orderOf (g₀ * c * g₀⁻¹) = orderOf c := by
      rw [← MulAut.conj_apply]
      exact orderOf_injective (MulAut.conj g₀).toMonoidHom (MulAut.conj g₀).injective _
    have hcor : orderOf c = p ^ e := by
      change orderOf (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6
        (CFSG.SeitzReduction.E6Pilot.corootTuple α s₀)) = p ^ e
      exact orderOf_rootDiagUnit_corootTupleE (by omega : p ≠ 2) hα hs₀ord
    rw [← hβy, hyβ, hconj, hcor]
  exact ⟨y, hyJ, hyT, hyord⟩

end ExcFrames

end CFSG.StandardType
