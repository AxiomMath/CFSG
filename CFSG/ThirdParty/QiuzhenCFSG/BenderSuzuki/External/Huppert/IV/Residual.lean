module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV residuals
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v

/-- The `p`-residual `O^p(G)`, as the intersection of all normal subgroups
with `p`-group quotient. -/
public noncomputable def hktPResidual (p : ℕ) (G : Type u) [Group G] :
    Subgroup G :=
  ⨅ R : {N : Subgroup G // ∃ hN : N.Normal,
      letI : N.Normal := hN
      IsPGroup p (G ⧸ N)}, R.1

public theorem hktPResidual_normal
    {Q : Type u} [Group Q] {q : ℕ} :
    (hktPResidual q Q).Normal := by
  dsimp [hktPResidual]
  exact Subgroup.normal_iInf_normal (fun R => R.2.choose)

public theorem hktPResidual_le
    {Q : Type u} [Group Q] {q : ℕ} (N : Subgroup Q) (hN : N.Normal)
    (hquot : letI : N.Normal := hN; IsPGroup q (Q ⧸ N)) :
    hktPResidual q Q ≤ N := by
  let R : {N : Subgroup Q // ∃ hN : N.Normal,
      letI : N.Normal := hN
      IsPGroup q (Q ⧸ N)} := ⟨N, ⟨hN, hquot⟩⟩
  exact iInf_le (fun R : {N : Subgroup Q // ∃ hN : N.Normal,
      letI : N.Normal := hN
      IsPGroup q (Q ⧸ N)} => R.1) R

/-- A normal `p`-complement makes the `p`-residual proper whenever `p`
divides the ambient group order. -/
public theorem hktPResidual_ne_top_of_hasNormalPComplement_of_dvd_card
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcomp : HasNormalPComplement p G) (hp_dvd : p ∣ Nat.card G) :
    hktPResidual p G ≠ (⊤ : Subgroup G) := by
  rcases hcomp with ⟨N, hNnormal, hNcop, hquotp⟩
  have hres_le : hktPResidual p G ≤ N :=
    hktPResidual_le N hNnormal hquotp
  intro hres_top
  have hNtop : N = ⊤ := top_unique (by simpa [hres_top] using hres_le)
  have hp_not_dvd_N : ¬ p ∣ Nat.card N :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hNcop
  exact hp_not_dvd_N (by simpa [hNtop] using hp_dvd)

public theorem hkt_pi_isPGroup
    {ι : Type*} [Finite ι]
    {G : ι → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    {p : ℕ} [Fact p.Prime] (hG : ∀ i, IsPGroup p (G i)) :
    IsPGroup p ((i : ι) → G i) := by
  classical
  letI := Fintype.ofFinite ι
  choose n hn using fun i =>
    (IsPGroup.iff_card (p := p) (G := G i)).mp (hG i)
  refine (IsPGroup.iff_card (p := p) (G := (i : ι) → G i)).mpr ?_
  refine ⟨∑ i, n i, ?_⟩
  calc
    Nat.card ((i : ι) → G i) = ∏ i, Nat.card (G i) := Nat.card_pi
    _ = ∏ i, p ^ n i := by simp [hn]
    _ = p ^ ∑ i, n i := by
      simpa using (Finset.prod_pow_eq_pow_sum Finset.univ n p)

public theorem hktPResidual_quotient_isPGroup
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime] :
    letI : (hktPResidual q Q).Normal := hktPResidual_normal (Q := Q) (q := q)
    IsPGroup q (Q ⧸ hktPResidual q Q) := by
  classical
  -- Standard residual fact: `G/O^q(G)` embeds in the product of all
  -- `q`-group quotients `G/N`.
  letI : ∀ R : {N : Subgroup Q // ∃ hN : N.Normal,
      letI : N.Normal := hN
      IsPGroup q (Q ⧸ N)}, R.1.Normal := fun R => R.2.choose
  let diag0 : Q →* ((R : {N : Subgroup Q // ∃ hN : N.Normal,
      letI : N.Normal := hN
      IsPGroup q (Q ⧸ N)}) → Q ⧸ R.1) :=
    { toFun := fun x R => QuotientGroup.mk' R.1 x
      map_one' := by
        ext R
        simp
      map_mul' := by
        intro x y
        ext R
        simp }
  have hker : hktPResidual q Q ≤ diag0.ker := by
    intro x hx
    change diag0 x = 1
    ext R
    change QuotientGroup.mk' R.1 x = 1
    exact (QuotientGroup.eq_one_iff (N := R.1) x).mpr
      ((Subgroup.mem_iInf.mp hx) R)
  have hker_eq : diag0.ker = hktPResidual q Q := by
    ext x
    constructor
    · intro hx
      dsimp [hktPResidual]
      exact Subgroup.mem_iInf.mpr (fun R => by
        have hcoord : QuotientGroup.mk' R.1 x = 1 := by
          simpa [diag0] using congrFun hx R
        exact (QuotientGroup.eq_one_iff (N := R.1) x).mp hcoord)
    · intro hx
      exact hker hx
  letI : (hktPResidual q Q).Normal := hktPResidual_normal (Q := Q) (q := q)
  let diag : Q ⧸ hktPResidual q Q →*
      ((R : {N : Subgroup Q // ∃ hN : N.Normal,
        letI : N.Normal := hN
        IsPGroup q (Q ⧸ N)}) → Q ⧸ R.1) :=
    QuotientGroup.lift (hktPResidual q Q) diag0 hker
  have hdiag_inj : Function.Injective diag := by
    refine (MonoidHom.ker_eq_bot_iff diag).1 ?_
    calc
      diag.ker = Subgroup.map (QuotientGroup.mk' (hktPResidual q Q)) diag0.ker := by
        simpa [diag] using
          (QuotientGroup.ker_lift (N := hktPResidual q Q) (φ := diag0) hker)
      _ = Subgroup.map (QuotientGroup.mk' (hktPResidual q Q)) (hktPResidual q Q) := by
        rw [hker_eq]
      _ = ⊥ := QuotientGroup.map_mk'_self (N := hktPResidual q Q)
  have hprod :
      IsPGroup q ((R : {N : Subgroup Q // ∃ hN : N.Normal,
        letI : N.Normal := hN
        IsPGroup q (Q ⧸ N)}) → Q ⧸ R.1) :=
    hkt_pi_isPGroup (fun R => R.2.choose_spec)
  exact IsPGroup.of_injective (hG := hprod) (ϕ := diag) hdiag_inj

/-- A quotient of a group with top `p`-residual again has top `p`-residual. -/
public theorem hktPResidual_quotient_eq_top_of_eq_top
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (M : Subgroup G) [M.Normal]
    (hres : hktPResidual p G = ⊤) :
    hktPResidual p (G ⧸ M) = ⊤ := by
  classical
  apply top_unique
  intro x _hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M x
  rw [hktPResidual, Subgroup.mem_iInf]
  intro R
  have hRnormal : R.1.Normal := R.2.choose
  letI : R.1.Normal := hRnormal
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let N : Subgroup G := R.1.comap q
  have hNnormal : N.Normal := hRnormal.comap q
  letI : N.Normal := hNnormal
  have hM_le_N : M ≤ N := by
    simpa [N, q] using QuotientGroup.le_comap_mk' M R.1
  have hNmap : N.map q = R.1 := by
    simpa [N, q] using
      Subgroup.map_comap_eq_self_of_surjective
        (f := q) (QuotientGroup.mk'_surjective M) R.1
  let e : (G ⧸ N) ≃* ((G ⧸ M) ⧸ R.1) :=
    (QuotientGroup.quotientQuotientEquivQuotient
      (N := M) (M := N) hM_le_N).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hNmap)
  have hquotG : IsPGroup p (G ⧸ N) :=
    R.2.choose_spec.of_equiv e.symm
  have hres_le : hktPResidual p G ≤ N :=
    hktPResidual_le N hNnormal hquotG
  have hg_res : g ∈ hktPResidual p G := by
    rw [hres]
    simp
  exact hres_le hg_res

public theorem hktPResidual_invariant
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (phi : G ≃* G) :
    ∀ g : G, g ∈ hktPResidual p G ↔ phi g ∈ hktPResidual p G := by
  classical
  have hforward :
      ∀ (psi : G ≃* G) (g : G),
        g ∈ hktPResidual p G → psi g ∈ hktPResidual p G := by
    intro psi g hg
    rw [hktPResidual, Subgroup.mem_iInf] at hg ⊢
    intro R
    let N : Subgroup G := R.1
    let Npre : Subgroup G := N.comap psi.toMonoidHom
    have hNnormal : N.Normal := R.2.choose
    letI : N.Normal := hNnormal
    have hNpreNormal : Npre.Normal := hNnormal.comap psi.toMonoidHom
    letI : Npre.Normal := hNpreNormal
    let qmap : G ⧸ Npre →* G ⧸ N :=
      QuotientGroup.map (N := Npre) N psi.toMonoidHom (by
        intro x hx
        exact hx)
    have hqmap_bij : Function.Bijective qmap := by
      constructor
      · intro x y hxy
        obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Npre x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Npre y
        apply QuotientGroup.eq_iff_div_mem.mpr
        have hquot :
            QuotientGroup.mk' N (psi a) =
              QuotientGroup.mk' N (psi b) := by
          simpa [qmap] using hxy
        have hmem : psi a / psi b ∈ N :=
          QuotientGroup.eq_iff_div_mem.mp hquot
        change psi (a / b) ∈ N
        simpa using hmem
      · intro y
        obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N y
        refine ⟨QuotientGroup.mk' Npre (psi.symm a), ?_⟩
        simp [qmap]
    let qequiv : (G ⧸ Npre) ≃* (G ⧸ N) :=
      MulEquiv.ofBijective qmap hqmap_bij
    have hquotP : IsPGroup p (G ⧸ N) := R.2.choose_spec
    have hpreP : IsPGroup p (G ⧸ Npre) :=
      hquotP.of_equiv qequiv.symm
    let Rpre : {N : Subgroup G // ∃ hN : N.Normal,
        letI : N.Normal := hN
        IsPGroup p (G ⧸ N)} :=
      ⟨Npre, hNpreNormal, hpreP⟩
    exact hg Rpre
  intro g
  constructor
  · exact hforward phi g
  · intro hg
    have := hforward phi.symm (phi g) hg
    simpa using this

public noncomputable def hktAbelianPResidual
    (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  commutator G ⊔ hktPResidual p G


public theorem commutator_le_hktAbelianPResidual
    {Q : Type u} [Group Q] {q : ℕ} :
    commutator Q ≤ hktAbelianPResidual q Q := by
  dsimp [hktAbelianPResidual]
  exact le_sup_left

public theorem hktPResidual_le_hktAbelianPResidual
    {Q : Type u} [Group Q] {q : ℕ} :
    hktPResidual q Q ≤ hktAbelianPResidual q Q := by
  dsimp [hktAbelianPResidual]
  exact le_sup_right

public theorem hktAbelianPResidual_normal
    {Q : Type u} [Group Q] {q : ℕ} :
    (hktAbelianPResidual q Q).Normal := by
  letI : (hktPResidual q Q).Normal := hktPResidual_normal (Q := Q) (q := q)
  dsimp [hktAbelianPResidual]
  infer_instance

public theorem hktAbelianPResidual_quotient_isPGroup
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime] :
    letI : (hktAbelianPResidual q Q).Normal :=
      hktAbelianPResidual_normal (Q := Q) (q := q)
    IsPGroup q (Q ⧸ hktAbelianPResidual q Q) := by
  classical
  -- This is the abelian `q`-residual kernel `G'(q)` in Huppert IV.3.7:
  -- quotient the `q`-residual further by the commutator subgroup.
  letI : (hktPResidual q Q).Normal := hktPResidual_normal (Q := Q) (q := q)
  letI : (hktAbelianPResidual q Q).Normal :=
    hktAbelianPResidual_normal (Q := Q) (q := q)
  have hle : hktPResidual q Q ≤ hktAbelianPResidual q Q :=
    hktPResidual_le_hktAbelianPResidual (Q := Q) (q := q)
  have hres : IsPGroup q (Q ⧸ hktPResidual q Q) :=
    hktPResidual_quotient_isPGroup (Q := Q) (q := q)
  have hquot :
      IsPGroup q
        ((Q ⧸ hktPResidual q Q) ⧸
          Subgroup.map (QuotientGroup.mk' (hktPResidual q Q))
            (hktAbelianPResidual q Q)) :=
    hres.to_quotient
      (Subgroup.map (QuotientGroup.mk' (hktPResidual q Q))
        (hktAbelianPResidual q Q))
  let e :
      ((Q ⧸ hktPResidual q Q) ⧸
          Subgroup.map (QuotientGroup.mk' (hktPResidual q Q))
            (hktAbelianPResidual q Q)) ≃*
        Q ⧸ hktAbelianPResidual q Q :=
    QuotientGroup.quotientQuotientEquivQuotient
      (N := hktPResidual q Q) (M := hktAbelianPResidual q Q) hle
  exact hquot.of_equiv e


public theorem hktAbelianPResidual_le
    {Q : Type u} [Group Q] {q : ℕ} {N : Subgroup Q}
    (hcomm : commutator Q ≤ N) (hpResidual : hktPResidual q Q ≤ N) :
    hktAbelianPResidual q Q ≤ N := by
  dsimp [hktAbelianPResidual]
  exact sup_le hcomm hpResidual


end External
end CFSG.BenderSuzuki
