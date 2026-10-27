module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SzWeights

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.B45Sz
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b

private lemma map_iSup_ne_le {k V E : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup E] [Module k E] {ι : Type*} (f : V →ₗ[k] E) (p : ι → Submodule k V)
    (q : ι → Submodule k E) (h : ∀ i, Submodule.map f (p i) ≤ q i) (w : ι) :
    Submodule.map f (⨆ (i) (_ : i ≠ w), p i) ≤ ⨆ (i) (_ : i ≠ w), q i := by
  rw [show (⨆ (i) (_ : i ≠ w), p i) = ⨆ i : {i : ι // i ≠ w}, p i from
      (iSup_subtype'' {i | i ≠ w} p).symm,
    show (⨆ (i) (_ : i ≠ w), q i) = ⨆ i : {i : ι // i ≠ w}, q i from
      (iSup_subtype'' {i | i ≠ w} q).symm,
    Submodule.map_iSup]
  refine iSup_le fun i => (h i.1).trans ?_
  exact le_iSup (fun j : {j : ι // j ≠ w} => q j.1) i

theorem szProbe {K : Type} [Field K] [CharP K 2] [Fintype K]
    {m : ℕ} (k : Type) [Field k] [Algebra K k] [CharP k 2] [IsAlgClosed k] {W : Type}
    [AddCommGroup W] [Module k W] [Module.Finite k W] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (σ : Representation k (suzukiGroup m K) W) (u : W) (hu : u ≠ 0)
    (hfix : ∀ x ∈ szUp m K, σ x u = u) (x₀ : ZMod (2 ^ (2 * m + 1) - 1))
    (hwt : ∀ l : Kˣ, σ (szD K m l) u = ((wchar1 (K := K) k x₀ l : kˣ) : k) • u) :
    ∃ J : Finset (Fin (2 * m + 1)), hw m J = x₀ ∧
      ∀ w ∈ wtSet m J, ∃ u' ∈ Submodule.span k (Set.range fun g => σ g u), u' ≠ 0 ∧
        ∀ l : Kˣ, σ (szD K m l) u' = ((wchar1 (K := K) k w l : kˣ) : k) • u' := by
  classical
  let M : Submodule k W := Submodule.span k (Set.range fun g : ↥(suzukiGroup m K) => σ g u)
  have huM : u ∈ M := Submodule.subset_span ⟨1, by simp⟩
  have hMinv : ∀ g : ↥(suzukiGroup m K), ∀ v ∈ M, σ g v ∈ M := by
    intro g v hv
    have hmap : Submodule.map (σ g) M ≤ M := by
      show Submodule.map (σ g)
          (Submodule.span k (Set.range fun h : ↥(suzukiGroup m K) => σ h u)) ≤
        Submodule.span k (Set.range fun h : ↥(suzukiGroup m K) => σ h u)
      rw [Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨y, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by
        show σ (g * h) u = σ g (σ h u)
        rw [map_mul, Module.End.mul_apply]⟩
    exact hmap (Submodule.mem_map_of_mem hv)
  let Msub : Subrepresentation σ := ⟨M, hMinv⟩
  have hMne : M ≠ ⊥ := by
    intro h
    have : u ∈ (⊥ : Submodule k W) := h ▸ huM
    exact hu ((Submodule.mem_bot (R := k)).mp this)
  haveI hMsubNontriv : Nontrivial Msub.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hMne
  haveI hMsubFin : Module.Finite k Msub.toSubmodule := by
    haveI : Module.Finite k (⊤ : Submodule k W) :=
      Module.Finite.equiv (Submodule.topEquiv (R := k) (M := W)).symm
    exact Submodule.finiteDimensional_of_le (le_top : Msub.toSubmodule ≤ ⊤)
  obtain ⟨N, hN⟩ := exists_isCoatom_subrep Msub.toRepresentation
  have hEirr : N.quotient.IsIrreducible :=
    quotient_isIrreducible_of_isCoatom Msub.toRepresentation N hN
  let uM : Msub.toSubmodule := ⟨u, huM⟩
  have hūne : N.toSubmodule.mkQ uM ≠ 0 := by
    intro h0
    have humem : uM ∈ N.toSubmodule := by
      rw [Submodule.mkQ_apply] at h0
      exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp h0
    have htop : N.toSubmodule = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro x
      have hx : (x : W) ∈ Submodule.span k (Set.range fun g : ↥(suzukiGroup m K) => σ g u) :=
        x.2
      refine Submodule.span_induction
        (p := fun y hy => (⟨y, hy⟩ : Msub.toSubmodule) ∈ N.toSubmodule) ?_ ?_ ?_ ?_ hx
      · intro y hy
        rcases hy with ⟨g, rfl⟩
        exact N.apply_mem_toSubmodule g humem
      · exact N.toSubmodule.zero_mem
      · intro y z hy hz ihy ihz
        show (⟨y + z, Submodule.add_mem M hy hz⟩ : Msub.toSubmodule) ∈ N.toSubmodule
        rw [show (⟨y + z, Submodule.add_mem M hy hz⟩ : Msub.toSubmodule) =
          (⟨y, hy⟩ : Msub.toSubmodule) + ⟨z, hz⟩ from rfl]
        exact N.toSubmodule.add_mem ihy ihz
      · intro a y hy ihy
        show (⟨a • y, Submodule.smul_mem M a hy⟩ : Msub.toSubmodule) ∈ N.toSubmodule
        rw [show (⟨a • y, Submodule.smul_mem M a hy⟩ : Msub.toSubmodule) =
          a • (⟨y, hy⟩ : Msub.toSubmodule) from rfl]
        exact N.toSubmodule.smul_mem a ihy
    exact hN.1 (Subrepresentation.toSubmodule_injective htop)
  let ū : Msub.toSubmodule ⧸ N.toSubmodule := N.toSubmodule.mkQ uM
  obtain ⟨A, hA, ⟨Φ⟩⟩ := exists_szT_equiv (a := m) (K := K) k hK N.quotient hEirr
  obtain ⟨J, hJ⟩ := exists_szIdx_eq (m := m) hA
  subst A
  let y : (szIdx m J → Fin 4) → k := Φ.symm ū
  have hy_ne : y ≠ 0 := by
    intro hy0
    apply hūne
    have h1 : Φ y = 0 := by rw [hy0, map_zero]
    have h2 : Φ y = ū := Φ.apply_symm_apply ū
    rw [h2] at h1
    exact h1
  have hπeq : ∀ (g : ↥(suzukiGroup m K)) (v : Msub.toSubmodule),
      N.toSubmodule.mkQ (Msub.toRepresentation g v) = N.quotient g (N.toSubmodule.mkQ v) := by
    intro g v
    rfl
  have hy_fix : ∀ h ∈ szUp m K, matRep (szT k hK (szIdx m J)) h y = y := by
    intro h hh
    have hq : N.quotient h ū = ū := by
      have h1 : N.quotient h (N.toSubmodule.mkQ uM) = N.toSubmodule.mkQ uM := by
        rw [← hπeq h uM]
        congr 1
        exact Subtype.ext (hfix h hh)
      exact h1
    have h2 : Φ.symm (N.quotient h ū) = matRep (szT k hK (szIdx m J)) h (Φ.symm ū) :=
      congr($((Φ.symm).toIntertwiningMap.isIntertwining' h) ū)
    rw [← h2, hq]
  have hy_weight : ∀ l : Kˣ, matRep (szT k hK (szIdx m J)) (szD K m l) y =
      ((wchar1 (K := K) k x₀ l : kˣ) : k) • y := by
    intro l
    have hq : N.quotient (szD K m l) ū = ((wchar1 (K := K) k x₀ l : kˣ) : k) • ū := by
      have h1 : N.quotient (szD K m l) (N.toSubmodule.mkQ uM) =
          N.toSubmodule.mkQ (((wchar1 (K := K) k x₀ l : kˣ) : k) • uM) := by
        rw [← hπeq (szD K m l) uM]
        congr 1
        exact Subtype.ext (hwt l)
      rwa [map_smul] at h1
    have h2 : Φ.symm (N.quotient (szD K m l) ū) =
        matRep (szT k hK (szIdx m J)) (szD K m l) (Φ.symm ū) :=
      congr($((Φ.symm).toIntertwiningMap.isIntertwining' (szD K m l)) ū)
    rw [← h2, hq]
    rw [show Φ.symm (((wchar1 (K := K) k x₀ l : kˣ) : k) • ū) =
        ((wchar1 (K := K) k x₀ l : kˣ) : k) • y
      from (Φ.symm).toLinearEquiv.map_smul _ _]
  obtain ⟨hfixed, -⟩ := szT_fixed_irreducible (a := m) (K := K) k hK hA
  have hy_fixedsub : y ∈ fixedSub (matRep (szT k hK (szIdx m J))) (szUp m K) := by
    rw [mem_fixedSub]
    exact hy_fix
  have hy_span : y ∈ Submodule.span k {hwS k (szIdx m J)} := by
    rw [← hfixed]
    exact hy_fixedsub
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy_span
  have hc_ne : c ≠ 0 := by
    intro h0
    apply hy_ne
    rw [← hc, h0, zero_smul]
  have hx0 : x₀ = hw m J := by
    apply wchar1_injective k hK
    refine MonoidHom.ext (fun l => ?_)
    have h1 := hy_weight l
    rw [← hc, map_smul, szT_hwS_weight k hK J l] at h1
    have hv_ne : c • hwS k (szIdx m J) ≠ 0 := smul_ne_zero hc_ne (hwS_ne_zero k (szIdx m J))
    have h2 : ((wchar1 (K := K) k (hw m J) l : kˣ) : k) • (c • hwS k (szIdx m J)) =
        ((wchar1 (K := K) k x₀ l : kˣ) : k) • (c • hwS k (szIdx m J)) := by
      rw [show ((wchar1 (K := K) k (hw m J) l : kˣ) : k) • (c • hwS k (szIdx m J)) =
          c • (((wchar1 (K := K) k (hw m J) l : kˣ) : k) • hwS k (szIdx m J))
        from smul_comm _ _ _]
      exact h1
    exact (Units.ext (smul_left_injective k hv_ne h2)).symm
  refine ⟨J, hx0.symm, ?_⟩
  intro w hwmem
  let τM : Representation k Kˣ Msub.toSubmodule := Msub.toRepresentation.comp (szD K m)
  let τE : Representation k Kˣ (Msub.toSubmodule ⧸ N.toSubmodule) := N.quotient.comp (szD K m)
  let p : ZMod (2 ^ (2 * m + 1) - 1) → Submodule k Msub.toSubmodule :=
    fun x => weightSpace τM (wchar1 (K := K) k x)
  let q : ZMod (2 ^ (2 * m + 1) - 1) → Submodule k (Msub.toSubmodule ⧸ N.toSubmodule) :=
    fun x => weightSpace τE (wchar1 (K := K) k x)
  obtain ⟨v, hv_ne, hv_wt⟩ := szT_exists_weight k hK J hwmem
  let s : Msub.toSubmodule ⧸ N.toSubmodule := Φ v
  have hs_ne : s ≠ 0 := by
    intro hs0
    apply hv_ne
    have h1 : Φ v = Φ 0 := by
      change s = Φ 0
      rw [hs0, map_zero]
    exact EquivLike.injective Φ h1
  have hs_wt : s ∈ q w := by
    rw [mem_weightSpace]
    intro l
    change N.quotient (szD K m l) (Φ v) =
      ((wchar1 (K := K) k w l : kˣ) : k) • Φ v
    have hΦ : N.quotient (szD K m l) (Φ v) =
        Φ (matRep (szT k hK (szIdx m J)) (szD K m l) v) :=
      (congr($((Φ.toIntertwiningMap.isIntertwining' (szD K m l))) v)).symm
    rw [hΦ, hv_wt l]
    exact (Φ.toLinearEquiv).map_smul _ _
  have hpne : p w ≠ ⊥ := by
    intro hpbot
    have hp_top : (⨆ x, p x) = ⊤ := iSup_weightSpace_wchar1 k hK τM
    have htop' : (⊤ : Submodule k Msub.toSubmodule) = ⨆ (x) (_ : x ≠ w), p x := by
      rw [← hp_top, iSup_split_single p w, hpbot, bot_sup_eq]
    obtain ⟨mv, hmv⟩ := Submodule.mkQ_surjective N.toSubmodule s
    have hm_top : mv ∈ ⨆ (x) (_ : x ≠ w), p x := by
      rw [← htop']
      exact Submodule.mem_top
    have hpq : ∀ x, Submodule.map (N.toSubmodule.mkQ) (p x) ≤ q x := by
      intro x
      rintro _ ⟨v₀, hv₀, rfl⟩
      change ∀ l, τM l v₀ = ((wchar1 (K := K) k x l : kˣ) : k) • v₀ at hv₀
      change ∀ l, τE l (N.toSubmodule.mkQ v₀) =
        ((wchar1 (K := K) k x l : kˣ) : k) • N.toSubmodule.mkQ v₀
      intro l
      calc τE l (N.toSubmodule.mkQ v₀)
          = N.toSubmodule.mkQ (τM l v₀) := (hπeq (szD K m l) v₀).symm
        _ = N.toSubmodule.mkQ ((wchar1 (K := K) k x l : k) • v₀) := by rw [hv₀ l]
        _ = (wchar1 (K := K) k x l : k) • N.toSubmodule.mkQ v₀ :=
            (N.toSubmodule.mkQ).map_smul _ _
    have hs_sub : s ∈ ⨆ (x) (_ : x ≠ w), q x := by
      have hle := map_iSup_ne_le (N.toSubmodule.mkQ) p q hpq w
      have hmaps : N.toSubmodule.mkQ mv ∈
          Submodule.map (N.toSubmodule.mkQ) (⨆ (x) (_ : x ≠ w), p x) :=
        Submodule.mem_map_of_mem hm_top
      have := hle hmaps
      rwa [hmv] at this
    have hq_indep : iSupIndep q := iSupIndep_weightSpace_wchar1 k hK τE
    have hs_bot : s ∈ (q w ⊓ ⨆ (x) (_ : x ≠ w), q x) := ⟨hs_wt, hs_sub⟩
    have hdisj := hq_indep w
    rw [disjoint_iff] at hdisj
    have hs0 : s = 0 := by
      have hmem : s ∈ (⊥ : Submodule k (Msub.toSubmodule ⧸ N.toSubmodule)) := hdisj ▸ hs_bot
      exact (Submodule.mem_bot (R := k)).mp hmem
    exact hs_ne hs0
  obtain ⟨m', hm'mem, hm'ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  refine ⟨(m' : W), m'.2, ?_, ?_⟩
  · intro h0
    exact hm'ne (Subtype.ext h0)
  · intro l
    have hwt' : τM l m' = (wchar1 (K := K) k w l : k) • m' :=
      (mem_weightSpace τM (wchar1 (K := K) k w) m').mp hm'mem l
    exact congrArg Subtype.val hwt'

end CFSG.StandardType.ReeB2Fixed
