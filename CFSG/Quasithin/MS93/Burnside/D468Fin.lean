module

public import CFSG.Quasithin.MS93.Burnside.D468Act
public import CFSG.Quasithin.MS93.Burnside.D468Core
public import CFSG.Quasithin.MS93.S46R468G
public import CFSG.Quasithin.MS93.S46R468M4

public section

namespace CFSG.Yardstones.M71b2fd3d34b9

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
  CFSG.Quasithin.MS93.S46R
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideD468_exists_isPtOn (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) :
    ∃ P, IsPtOn (puAmalgam c.pu.le) x β P := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  obtain ⟨hW2, -⟩ := I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ
  have hWne : fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) ≠ ⊥ := fun he => by
    rw [he, finrank_bot] at hW2
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  obtain ⟨P, hP, -, -⟩ := exists_isPtOn_span h464 h465 c hx hxβ hψs hψ hv hv0
  exact ⟨P, hP⟩

theorem burnsideD468_exists_isPtOn_mem_ptQ (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {z : (puAmalgam c.pu.le).Universal}
    (hz : z ∈ Qv (puAmalgam c.pu.le) β) (hzx : z ∉ Qv (puAmalgam c.pu.le) x) :
    ∃ P, IsPtOn (puAmalgam c.pu.le) x β P ∧ z ∈ ptQ (puAmalgam c.pu.le) x P := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  obtain ⟨P₀, hP₀⟩ := burnsideD468_exists_isPtOn h464 h465 c hx hxβ
  obtain ⟨ψ, hψs, hψU, -, hT⟩ := exists_coord_pt h464 h465 h466a c hx hxβ hP₀
  have hzs : z ∈ stab (puAmalgam c.pu.le) x := qv_le_stab_of_adj _ hxβ.symm hz
  have hzT : toSL3 ψ ⟨z, hzs⟩ ∈ (qLn : Subgroup (SL3 F)) := by
    rw [← hT]
    exact mem_natImage.mpr ⟨⟨z, hzs⟩, hz, rfl⟩
  obtain ⟨b, d, hbd⟩ := CFSG.Quasithin.MS93.mem_qLn_iff_uniTri.mp hzT
  have hw0 : (![b, d, 0] : Fin 3 → F) ≠ 0 := by
    intro hw
    apply hzx
    have hb : b = 0 := by simpa using congrFun hw 0
    have hd : d = 0 := by simpa using congrFun hw 1
    rw [hb, hd, uniTri_zero] at hbd
    exact (toSL3_eq_one_iff_mem_qv c.pu c.via hx hψU _).mp hbd.symm
  have hwW : (![b, d, 0] : Fin 3 → F) ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) := by
    rw [hT, fixN_qLn, mem_ln01]
    rfl
  obtain ⟨P, hP, -, hPc⟩ := exists_isPtOn_span h464 h465 c hx hxβ hψs hψU hwW hw0
  have hPβ : P ≤ Usup (puAmalgam c.pu.le) x β := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  refine ⟨P, hP, hzs, ?_, fun y hy => ?_⟩
  ·
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β (h464' x β hx hxβ (hPβ ha)))
      z hz).symm
  ·
    obtain ⟨u, hu, ζ, hζ, rfl⟩ := I466b.exists_uloc_mul_zloc c.pu hfull hx hy
    have hζz : ζ * z = z * ζ :=
      (Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab c.pu hfull hx hζ) z hzs).symm
    have e1 : ⁅u * ζ, z⁆ = ⁅u, z⁆ := by
      simp only [commutatorElement_def]
      calc u * ζ * z * (u * ζ)⁻¹ * z⁻¹ = u * (ζ * z) * ζ⁻¹ * u⁻¹ * z⁻¹ := by group
        _ = u * (z * ζ) * ζ⁻¹ * u⁻¹ * z⁻¹ := by rw [hζz]
        _ = u * z * u⁻¹ * z⁻¹ := by group
    rw [e1]
    have hmem : ⁅u, z⁆ ∈ Uloc c.pu.le L x := by
      have h1 : z * u * z⁻¹ ∈ Uloc c.pu.le L x :=
        (Subgroup.mem_normalizer_iff.mp (hψU.1 hzs) u).mp hu
      have e : ⁅u, z⁆ = u * (z * u * z⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ h1)
    refine (hPc ⟨_, hmem⟩).mpr ?_
    rw [natVec_commutator hψU ⟨z, hzs⟩ ⟨u, hu⟩ ⟨_, hmem⟩ rfl, ← hbd, uniTri_mulVec]
    refine Submodule.mem_span_singleton.mpr ⟨-(natVec hψU ⟨u, hu⟩ 2), ?_⟩
    funext k
    fin_cases k <;> simp <;> ring

theorem burnsideD468_exists_bad_line (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α₀ β₀ : Vtx (puAmalgam c.pu.le)}
    (hbad : ¬ S468At (puAmalgam c.pu.le) α₀ β₀) (hα₀ : IsMVtx (puAmalgam c.pu.le) α₀)
    (hα₀β₀ : (puAmalgam c.pu.le).treeGraph.Adj α₀ β₀) {x β : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    {r : (puAmalgam c.pu.le).Universal} (hrT : r ∈ Qv (puAmalgam c.pu.le) β)
    (hrP : r ∈ ptQ (puAmalgam c.pu.le) x P) (hrx : r ∉ Qv (puAmalgam c.pu.le) x) :
    ∃ μ, (puAmalgam c.pu.le).treeGraph.Adj x μ ∧ P ≤ Usup (puAmalgam c.pu.le) x μ ∧
      ∃ w ∈ Vv (puAmalgam c.pu.le) μ, ⁅w, r⁆ ∉ bzero c x := by
  by_contra hno
  push Not at hno
  have h464' := h464 G M T L F φ c
  let K : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {k | k ∈ stab (puAmalgam c.pu.le) x ∧
        ∀ μ, (puAmalgam c.pu.le).treeGraph.Adj x μ → P ≤ Usup (puAmalgam c.pu.le) x μ →
          ∀ w ∈ Vv (puAmalgam c.pu.le) μ, ⁅w, k⁆ ∈ bzero c x}
      one_mem' := ⟨Subgroup.one_mem _, fun _ _ _ w _ => by
        rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro k₁ k₂ ⟨hk₁, hk₁'⟩ ⟨hk₂, hk₂'⟩
        refine ⟨Subgroup.mul_mem _ hk₁ hk₂, fun μ hxμ hPμ w hw => ?_⟩
        have e : ⁅w, k₁ * k₂⁆ = ⁅w, k₁⁆ * (k₁ * ⁅w, k₂⁆ * k₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ (hk₁' μ hxμ hPμ w hw) ((Subgroup.mem_normalizer_iff.mp
          (stab_le_normalizer_bzero c x hk₁) _).mp (hk₂' μ hxμ hPμ w hw))
      inv_mem' := by
        rintro k ⟨hk, hk'⟩
        refine ⟨Subgroup.inv_mem _ hk, fun μ hxμ hPμ w hw => ?_⟩
        have e : ⁅w, k⁻¹⁆ = k⁻¹ * ⁅w, k⁆⁻¹ * k⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c x
          (Subgroup.inv_mem _ hk)) _).mp (Subgroup.inv_mem _ (hk' μ hxμ hPμ w hw)) }
  have hrK : r ∈ K := ⟨(mem_ptQ.mp hrP).1, hno⟩
  have hQK : Qv (puAmalgam c.pu.le) x ≤ K := fun q hq => ⟨qv_le_stab _ x hq, fun μ hxμ _ w hw =>
    zm_le_bzero c hx ((h465 G M T L F φ c x μ hx hxμ).2.2
      (Subgroup.commutator_mem_commutator (I466b.vv_le_vv_of_adj c.pu hx hxμ hw) hq))⟩
  have hKn : ∀ g ∈ stab (puAmalgam c.pu.le) x, (∀ p ∈ P, g * p * g⁻¹ ∈ P) →
      ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    rintro g hg hgP k ⟨hk, hk'⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hk) (Subgroup.inv_mem _ hg),
      fun μ hxμ hPμ w hw => ?_⟩
    have hg'x : g⁻¹ • x = x := MulAction.mem_stabilizer_iff.mp (Subgroup.inv_mem _ hg)
    have hxμ' : (puAmalgam c.pu.le).treeGraph.Adj x (g⁻¹ • μ) := by
      have := (adj_smul _ g⁻¹ x μ).mpr hxμ
      rwa [hg'x] at this
    have hU' : Usup (puAmalgam c.pu.le) x (g⁻¹ • μ) =
        (Usup (puAmalgam c.pu.le) x μ).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← usup_smul, hg'x]
    have hPμ' : P ≤ Usup (puAmalgam c.pu.le) x (g⁻¹ • μ) := by
      intro p hp
      rw [hU']
      refine ⟨g * p * g⁻¹, hPμ (hgP p hp), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ Vv (puAmalgam c.pu.le) (g⁻¹ • μ) := by
      rw [show Vv (puAmalgam c.pu.le) (g⁻¹ • μ) = (Vv _ μ).map (MulAut.conj g⁻¹).toMonoidHom from
        vi_smul _ g⁻¹ μ 2]
      exact conj_mem_map_conj hw
    have h1 := hk' _ hxμ' hPμ' _ hw'
    have e : ⁅w, g * k * g⁻¹⁆ = g * ⁅g⁻¹ * w * g⁻¹⁻¹, k⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c x hg) _).mp h1
  obtain ⟨ψ, hψs, hψU, hPc, hT⟩ := exists_coord_pt h464 h465 h466a c hx hxβ hP
  have hPU : P ≤ Uloc c.pu.le L x := le_uloc_of_isPtOn c hx hP
  have hQP : natImage ψ (ptQ (puAmalgam c.pu.le) x P) = qPt :=
    natImage_ptQ c hx hψs hψU hPU hPc
  have hroot : ∀ t ∈ Qv (puAmalgam c.pu.le) β ⊓ ptQ _ x P, ∃ hts : t ∈ stab (puAmalgam c.pu.le) x,
      ∃ b : F, toSL3 ψ ⟨t, hts⟩ = rootElt 0 2 b := by
    rintro t ⟨htT, htP⟩
    have hts : t ∈ stab (puAmalgam c.pu.le) x := (mem_ptQ.mp htP).1
    have h1 : toSL3 ψ ⟨t, hts⟩ ∈ (qLn : Subgroup (SL3 F)) := by
      rw [← hT]
      exact mem_natImage.mpr ⟨⟨t, hts⟩, htT, rfl⟩
    have h2 : toSL3 ψ ⟨t, hts⟩ ∈ (qPt : Subgroup (SL3 F)) := by
      rw [← hQP]
      exact mem_natImage.mpr ⟨⟨t, hts⟩, htP, rfl⟩
    obtain ⟨b, d, hbd⟩ := CFSG.Quasithin.MS93.mem_qLn_iff_uniTri.mp h1
    obtain ⟨a, b', hab⟩ := CFSG.Quasithin.MS93.mem_qPt_iff_uniTri.mp h2
    obtain ⟨-, -, hd⟩ := uniTri_eq_uniTri_iff.mp (hbd.trans hab.symm)
    refine ⟨hts, b, ?_⟩
    rw [← hbd, hd, rootElt02_eq_uniTri]
  have hone : ∀ t (hts : t ∈ stab (puAmalgam c.pu.le) x), toSL3 ψ ⟨t, hts⟩ = 1 →
      t ∈ Qv (puAmalgam c.pu.le) x := fun t hts h =>
    (toSL3_eq_one_iff_mem_qv c.pu c.via hx hψU ⟨t, hts⟩).mp h
  obtain ⟨hrs, b₀, hb₀⟩ := hroot r ⟨hrT, hrP⟩
  have hb₀0 : b₀ ≠ 0 := by
    rintro rfl
    exact hrx (hone r hrs (by rw [hb₀, rootElt02_eq_uniTri, uniTri_zero]))
  have hTK : Qv (puAmalgam c.pu.le) β ⊓ ptQ _ x P ≤ K := by
    intro t ht
    obtain ⟨hts, b₁, hb₁⟩ := hroot t ht
    by_cases hb₁0 : b₁ = 0
    · exact hQK (hone t hts (by rw [hb₁, hb₁0, rootElt02_eq_uniTri, uniTri_zero]))
    have hl : b₁ * b₀⁻¹ ≠ 0 := mul_ne_zero hb₁0 (inv_ne_zero hb₀0)
    obtain ⟨g, hg⟩ := toSL3_surjective hψs (diagPt (b₁ * b₀⁻¹) hl)
    have hgP : ∀ p ∈ P, (g : (puAmalgam c.pu.le).Universal) * p * (g : _)⁻¹ ∈ P := by
      intro p hp
      have hpU := hPU hp
      have hmem : (g : (puAmalgam c.pu.le).Universal) * p * (g : _)⁻¹ ∈ Uloc c.pu.le L x :=
        (Subgroup.mem_normalizer_iff.mp (hψU.1 g.2) p).mp hpU
      refine (hPc ⟨_, hmem⟩).mpr ?_
      have hp0 := (hPc ⟨p, hpU⟩).mp hp
      rw [natVec_conj hψU g ⟨p, hpU⟩ ⟨_, hmem⟩ rfl, hg, diagPt_mulVec]
      rw [mem_pt0] at hp0 ⊢
      simp [hp0.1, hp0.2]
    have hgr : (g : (puAmalgam c.pu.le).Universal) * r * (g : _)⁻¹ ∈ K :=
      hKn g g.2 hgP r hrK
    have hgrs : (g : (puAmalgam c.pu.le).Universal) * r * (g : _)⁻¹ ∈ stab _ x := hgr.1
    have hψeq : toSL3 ψ (g * ⟨r, hrs⟩ * g⁻¹) = toSL3 ψ ⟨t, hts⟩ := by
      rw [map_mul, map_mul, map_inv, hg, hb₀, hb₁, diagPt_conj_rootElt, mul_assoc,
        inv_mul_cancel₀ hb₀0, mul_one]
    have hq : ((g * ⟨r, hrs⟩ * g⁻¹)⁻¹ * ⟨t, hts⟩ : ↥(stab (puAmalgam c.pu.le) x)) ∈
        (toSL3 ψ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψeq, inv_mul_cancel]
    have hqx := hone _ _ (MonoidHom.mem_ker.mp hq)
    have e : t = ((g : (puAmalgam c.pu.le).Universal) * r * (g : _)⁻¹) *
        (((g * ⟨r, hrs⟩ * g⁻¹)⁻¹ * ⟨t, hts⟩ : ↥(stab (puAmalgam c.pu.le) x)) :
          (puAmalgam c.pu.le).Universal) := by
      simp
      group
    rw [e]
    exact Subgroup.mul_mem _ hgr (hQK hqx)
  obtain ⟨β', hxβ', hne, hPe⟩ := hP
  have hβ' : ¬ IsMVtx (puAmalgam c.pu.le) β' := (isMVtx_iff_of_adj _ hxβ').mp hx
  have hP' : IsPtOn (puAmalgam c.pu.le) x β' P := ⟨β, hxβ, Ne.symm hne, by rw [hPe, inf_comm]⟩
  have hPβ' : P ≤ Usup (puAmalgam c.pu.le) x β' := hPe ▸ inf_le_right
  apply not_commutator_vv_ptQ_le h464 h465 h466a c hbad hα₀ hα₀β₀ hx hxβ' hP'
  have hQs : ptQ (puAmalgam c.pu.le) x P ≤ stab _ x := fun t ht => (mem_ptQ.mp ht).1
  have hJ₁ : ∀ k ∈ Qv (puAmalgam c.pu.le) β ⊓ ptQ _ x P, ∀ w ∈ Vv (puAmalgam c.pu.le) β',
      ⁅w, k⁆ ∈ bzero c x := fun k hk w hw => (hTK hk).2 β' hxβ' hPβ' w hw
  have hJ₂ : ∀ k ∈ Qv (puAmalgam c.pu.le) β' ⊓ ptQ _ x P, ∀ w ∈ Vv (puAmalgam c.pu.le) β',
      ⁅w, k⁆ ∈ bzero c x := fun k hk w hw =>
    zm_le_bzero c hx (zh_le_zm _ hxβ' (commutator_vv_qv_le_zh c.pu h464' hβ'
      (Subgroup.commutator_mem_commutator hw hk.1)))
  have hall := burnsideD468_forall_bzero_of_le_sup c (inf_le_right.trans hQs)
    (inf_le_right.trans hQs) hJ₁ hJ₂
  have hQPle := ptQ_le_sup_qv_inf h464 h465 h466a c hx hxβ hxβ' (Ne.symm hne) hPe
  rw [Subgroup.commutator_le]
  intro w hw k hk
  exact hall k (hQPle hk) w hw

theorem burnsideD468_commutator_mem_bzero_of_mem_qv (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α β x μ : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hβx : (puAmalgam c.pu.le).treeGraph.Adj β x) {b : Subgroup (puAmalgam c.pu.le).Universal}
    (hb : IsPtOn (puAmalgam c.pu.le) α β b) (hαμ : (puAmalgam c.pu.le).treeGraph.Adj α μ)
    (hbμ : b ≤ Usup (puAmalgam c.pu.le) α μ) {w y : (puAmalgam c.pu.le).Universal}
    (hw : w ∈ Vv (puAmalgam c.pu.le) μ) (hwx : w ∈ Qv (puAmalgam c.pu.le) x)
    (hy : y ∈ Vv (puAmalgam c.pu.le) x) (hyb : y ∈ ptQ (puAmalgam c.pu.le) α b) :
    ⁅w, y⁆ ∈ bzero c α := by
  have h464' := h464 G M T L F φ c
  have hb2 : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hμ : ¬ IsMVtx (puAmalgam c.pu.le) μ := (isMVtx_iff_of_adj _ hαμ).mp hα
  have hyT : y ∈ Qv (puAmalgam c.pu.le) β := vv_le_qv_of_adj_isMVtx c hx hβx.symm hy
  have hbβ : b ≤ Usup (puAmalgam c.pu.le) α β := by
    obtain ⟨_, _, _, he⟩ := hb
    rw [he]
    exact inf_le_left
  have hbc : Nat.card ↥b = Fintype.card F := card_of_isPtOn h464 h465 c hα hαβ hb
  have hmeet : ∀ {ℓ₁ ℓ₂ : Vtx (puAmalgam c.pu.le)}, (puAmalgam c.pu.le).treeGraph.Adj α ℓ₁ →
      (puAmalgam c.pu.le).treeGraph.Adj α ℓ₂ →
      Usup (puAmalgam c.pu.le) α ℓ₁ ≠ Usup _ α ℓ₂ → b ≤ Usup (puAmalgam c.pu.le) α ℓ₁ →
      b ≤ Usup (puAmalgam c.pu.le) α ℓ₂ →
      b = Usup (puAmalgam c.pu.le) α ℓ₁ ⊓ Usup _ α ℓ₂ := by
    intro ℓ₁ ℓ₂ h₁ h₂ hne hb₁ hb₂
    have hc₁₂ := card_usup_inf_usup h464 h465 c hα h₁ h₂ hne
    have : Finite ↥(Usup (puAmalgam c.pu.le) α ℓ₁ ⊓ Usup _ α ℓ₂) :=
      Nat.finite_of_card_ne_zero (by rw [hc₁₂]; exact Fintype.card_ne_zero)
    exact Subgroup.eq_of_le_of_card_ge (le_inf hb₁ hb₂) (by rw [hc₁₂, hbc])
  have heμ : ⁅w, y⁆ ∈ Vv (puAmalgam c.pu.le) μ := by
    have hn := ptQ_le_normalizer_vv h464 h465 h466a c hα hαμ hbμ hyb
    have e1 : ⁅w, y⁆ = w * (y * w⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e1]
    exact Subgroup.mul_mem _ hw ((Subgroup.mem_normalizer_iff.mp hn _).mp (Subgroup.inv_mem _ hw))
  have heZ : ⁅w, y⁆ ∈ ZM (puAmalgam c.pu.le) x := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ ((h465 G M T L F φ c x β hx hβx.symm).2.2
      (Subgroup.commutator_mem_commutator hy hwx))
  have hcomm : ∀ k, (puAmalgam c.pu.le).treeGraph.Adj α k → b ≤ Usup (puAmalgam c.pu.le) α k →
      ∀ v ∈ Vv (puAmalgam c.pu.le) k, v * ⁅w, y⁆ = ⁅w, y⁆ * v := by
    intro k hαk hbk v hv
    by_cases hkμ : Usup (puAmalgam c.pu.le) α k = Usup _ α μ
    · have hV : Vv (puAmalgam c.pu.le) k = Vv _ μ :=
        vv_eq_of_usup_eq h464 h465 h466a c hα hαk hαμ hkμ
      exact vv_comm c.pu hb2 hμ (hV ▸ hv) heμ
    · have hr : y ∈ ptQ (puAmalgam c.pu.le) α (Usup _ α k ⊓ Usup _ α μ) := by
        rwa [← hmeet hαk hαμ hkμ hbk hbμ]
      exact commute_vv_commutator_vv_ptQ' h464 h465 h466a c hα hαk hαμ hkμ hv hw hr
  by_cases hμβ : Usup (puAmalgam c.pu.le) α μ = Usup _ α β
  · have hV : Vv (puAmalgam c.pu.le) μ = Vv _ β := vv_eq_of_usup_eq h464 h465 h466a c hα hαμ hαβ hμβ
    exact zm_le_bzero c hα (zh_le_zm _ hαβ (commutator_vv_qv_le_zh c.pu h464' hβ
      (Subgroup.commutator_mem_commutator (hV ▸ hw) hyT)))
  obtain ⟨R, hR, hRne⟩ := exists_other_pt h464 h465 c hα hαβ hb
  obtain ⟨t, ⟨htβ, htR⟩, htα⟩ := exists_mem_qv_inf_ptQ h464 h465 h466a c hα hαβ hR
  have htb : t ∉ ptQ (puAmalgam c.pu.le) α b := fun htb =>
    htα (qv_inf_ptQ_inf_ptQ_le h464 h465 h466a c hα hαβ hR hb hRne ⟨⟨htβ, htR⟩, htb⟩)
  have hts : t ∈ stab (puAmalgam c.pu.le) α := qv_le_stab_of_adj _ hαβ.symm htβ
  have htα' : t • α = α := MulAction.mem_stabilizer_iff.mp hts
  have hαm₁ : (puAmalgam c.pu.le).treeGraph.Adj α (t • μ) := by
    have := (adj_smul _ t α μ).mpr hαμ
    rwa [htα'] at this
  have hUm₁ : Usup (puAmalgam c.pu.le) α (t • μ) =
      (Usup (puAmalgam c.pu.le) α μ).map (MulAut.conj t).toMonoidHom := by
    rw [← usup_smul, htα']
  have hbm₁ : b ≤ Usup (puAmalgam c.pu.le) α (t • μ) := by
    intro a ha
    rw [hUm₁]
    have hca : t * a = a * t := Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β
      (h464' α β hα hαβ (hbβ ha))) t htβ
    refine ⟨a, hbμ ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hca, mul_assoc, mul_inv_cancel, mul_one]
  have hm₁μ : Usup (puAmalgam c.pu.le) α (t • μ) ≠ Usup _ α μ := by
    intro he
    apply htb
    have hn : t ∈ Subgroup.normalizer (Usup (puAmalgam c.pu.le) α μ : Set _) :=
      mem_normalizer_of_map_conj_eq (by rw [← hUm₁, he])
    have := mem_ptQ_of_mem_normalizer_usup h464 h465 c hα hαβ hαμ (Ne.symm hμβ) htβ hn
    rwa [← hmeet hαβ hαμ (Ne.symm hμβ) hbβ hbμ] at this
  have he₁ : t * ⁅w, y⁆ * t⁻¹ ∈ Vv (puAmalgam c.pu.le) (t • μ) := by
    rw [show Vv (puAmalgam c.pu.le) (t • μ) = (Vv _ μ).map (MulAut.conj t).toMonoidHom from
      vi_smul _ t μ 2]
    exact conj_mem_map_conj heμ
  have hdB : (t * ⁅w, y⁆ * t⁻¹)⁻¹ * ⁅w, y⁆ ∈ bzero c α := by
    have h1 : ⁅⁅w, y⁆⁻¹, t⁆ ∈ Usup (puAmalgam c.pu.le) x β := by
      rw [Usup, zv_of_isMVtx _ hx]
      exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ heZ) htβ
    have h2 : ⁅⁅w, y⁆⁻¹, t⁆⁻¹ ∈ ZH (puAmalgam c.pu.le) β :=
      Subgroup.inv_mem _ (h464' x β hx hβx.symm h1)
    have e2 : (t * ⁅w, y⁆ * t⁻¹)⁻¹ * ⁅w, y⁆ = ⁅⁅w, y⁆⁻¹, t⁆⁻¹ := by
      rw [commutatorElement_def ⁅w, y⁆⁻¹ t]
      group
    rw [e2]
    exact zm_le_bzero c hα (zh_le_zm _ hαβ h2)
  refine mem_bzero_of_mem_vv_mul' h464 h465 c hα hαμ hαm₁ (Ne.symm hm₁μ) heμ he₁ hdB (by group)
    fun k hαk hk v hv => ?_
  rw [← hmeet hαμ hαm₁ (Ne.symm hm₁μ) hbμ hbm₁] at hk
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm k hαk hk v hv).symm]
  exact Subgroup.one_mem _

theorem burnsideD468_commutator_mem_bzero_of_not_le (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {X β Y k μ : Vtx (puAmalgam c.pu.le)} (hX : IsMVtx (puAmalgam c.pu.le) X)
    (hXβ : (puAmalgam c.pu.le).treeGraph.Adj X β) (hY : IsMVtx (puAmalgam c.pu.le) Y)
    (hβY : (puAmalgam c.pu.le).treeGraph.Adj β Y) {A : Subgroup (puAmalgam c.pu.le).Universal}
    (hA : IsPtOn (puAmalgam c.pu.le) X β A) (hXk : (puAmalgam c.pu.le).treeGraph.Adj X k)
    (hAk : A ≤ Usup (puAmalgam c.pu.le) X k) (hkY : ¬ Vv (puAmalgam c.pu.le) k ≤ Qv _ Y)
    (hXμ : (puAmalgam c.pu.le).treeGraph.Adj X μ) (hAμ : A ≤ Usup (puAmalgam c.pu.le) X μ)
    {w₀ y : (puAmalgam c.pu.le).Universal} (hw₀ : w₀ ∈ Vv (puAmalgam c.pu.le) μ)
    (hyV : y ∈ Vv (puAmalgam c.pu.le) Y) (hyA : y ∈ ptQ (puAmalgam c.pu.le) X A) :
    ⁅w₀, y⁆ ∈ bzero c X := by
  by_contra hbad
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hXβ).mp hX
  have hk : ¬ IsMVtx (puAmalgam c.pu.le) k := (isMVtx_iff_of_adj _ hXk).mp hX
  have hYβ : (puAmalgam c.pu.le).treeGraph.Adj Y β := hβY.symm
  have hyT : y ∈ Qv (puAmalgam c.pu.le) β := vv_le_qv_of_adj_isMVtx c hY hYβ hyV
  have hAβ : A ≤ Usup (puAmalgam c.pu.le) X β := by
    obtain ⟨_, _, _, he⟩ := hA
    rw [he]
    exact inf_le_left
  have hAc : Nat.card ↥A = Fintype.card F := card_of_isPtOn h464 h465 c hX hXβ hA
  have hAmeet : ∀ {ℓ₁ ℓ₂ : Vtx (puAmalgam c.pu.le)}, (puAmalgam c.pu.le).treeGraph.Adj X ℓ₁ →
      (puAmalgam c.pu.le).treeGraph.Adj X ℓ₂ →
      Usup (puAmalgam c.pu.le) X ℓ₁ ≠ Usup _ X ℓ₂ → A ≤ Usup (puAmalgam c.pu.le) X ℓ₁ →
      A ≤ Usup (puAmalgam c.pu.le) X ℓ₂ →
      A = Usup (puAmalgam c.pu.le) X ℓ₁ ⊓ Usup _ X ℓ₂ := by
    intro ℓ₁ ℓ₂ h₁ h₂ hne hA₁ hA₂
    have hc₁₂ := card_usup_inf_usup h464 h465 c hX h₁ h₂ hne
    have : Finite ↥(Usup (puAmalgam c.pu.le) X ℓ₁ ⊓ Usup _ X ℓ₂) :=
      Nat.finite_of_card_ne_zero (by rw [hc₁₂]; exact Fintype.card_ne_zero)
    exact Subgroup.eq_of_le_of_card_ge (le_inf hA₁ hA₂) (by rw [hc₁₂, hAc])
  have hTXs : Qv (puAmalgam c.pu.le) β ≤ stab _ X := qv_le_stab_of_adj _ hXβ.symm
  have hμβ : Usup (puAmalgam c.pu.le) X μ ≠ Usup _ X β := by
    intro he
    have hV : Vv (puAmalgam c.pu.le) μ = Vv _ β := vv_eq_of_usup_eq h464 h465 h466a c hX hXμ hXβ he
    apply hbad
    have h1 : ⁅w₀, y⁆ ∈ ZH (puAmalgam c.pu.le) β :=
      commutator_vv_qv_le_zh c.pu h464' hβ (Subgroup.commutator_mem_commutator (hV ▸ hw₀) hyT)
    exact zm_le_bzero c hX (zh_le_zm _ hXβ h1)
  obtain ⟨R, hR, hRne⟩ := exists_other_pt h464 h465 c hX hXβ hA
  obtain ⟨yB, ⟨hyBT, hyBR⟩, hyBX⟩ := exists_mem_qv_inf_ptQ h464 h465 h466a c hX hXβ hR
  have hyBQ : yB ∉ ptQ (puAmalgam c.pu.le) X A := fun h =>
    hyBX (qv_inf_ptQ_inf_ptQ_le h464 h465 h466a c hX hXβ hR hA hRne ⟨⟨hyBT, hyBR⟩, h⟩)
  have hyBs : yB ∈ stab (puAmalgam c.pu.le) X := hTXs hyBT
  have hyBx : yB • X = X := MulAction.mem_stabilizer_iff.mp hyBs
  set μ' := yB • μ with hμ'def
  have hXμ' : (puAmalgam c.pu.le).treeGraph.Adj X μ' := by
    have := (adj_smul _ yB X μ).mpr hXμ
    rwa [hyBx] at this
  have hUμ' : Usup (puAmalgam c.pu.le) X μ' =
      (Usup (puAmalgam c.pu.le) X μ).map (MulAut.conj yB).toMonoidHom := by
    rw [hμ'def, ← usup_smul, hyBx]
  have hVμ' : Vv (puAmalgam c.pu.le) μ' =
      (Vv (puAmalgam c.pu.le) μ).map (MulAut.conj yB).toMonoidHom := vi_smul _ yB μ 2
  have hAμ' : A ≤ Usup (puAmalgam c.pu.le) X μ' := by
    intro a ha
    rw [hUμ']
    have hca : yB * a = a * yB := Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β
      (h464' X β hX hXβ (hAβ ha))) yB hyBT
    refine ⟨a, hAμ ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hca, mul_assoc, mul_inv_cancel, mul_one]
  have hμ'μ : Usup (puAmalgam c.pu.le) X μ' ≠ Usup _ X μ := by
    intro he
    apply hyBQ
    have hn : yB ∈ Subgroup.normalizer (Usup (puAmalgam c.pu.le) X μ : Set _) :=
      mem_normalizer_of_map_conj_eq (by rw [← hUμ', he])
    have := mem_ptQ_of_mem_normalizer_usup h464 h465 c hX hXβ hXμ (Ne.symm hμβ) hyBT hn
    rwa [← hAmeet hXβ hXμ (Ne.symm hμβ) hAβ hAμ] at this
  have hcomm : ∀ {ℓ ℓ' : Vtx (puAmalgam c.pu.le)}, (puAmalgam c.pu.le).treeGraph.Adj X ℓ →
      (puAmalgam c.pu.le).treeGraph.Adj X ℓ' → A ≤ Usup (puAmalgam c.pu.le) X ℓ →
      A ≤ Usup (puAmalgam c.pu.le) X ℓ' → ∀ u ∈ Vv (puAmalgam c.pu.le) ℓ,
      ∀ v ∈ Vv (puAmalgam c.pu.le) ℓ', u * ⁅v, y⁆ = ⁅v, y⁆ * u := by
    intro ℓ ℓ' hXℓ hXℓ' hAℓ hAℓ' u hu v hv
    by_cases he : Usup (puAmalgam c.pu.le) X ℓ = Usup _ X ℓ'
    · have hV : Vv (puAmalgam c.pu.le) ℓ = Vv _ ℓ' :=
        vv_eq_of_usup_eq h464 h465 h466a c hX hXℓ hXℓ' he
      have hℓ' : ¬ IsMVtx (puAmalgam c.pu.le) ℓ' := (isMVtx_iff_of_adj _ hXℓ').mp hX
      have hvy : ⁅v, y⁆ ∈ Vv (puAmalgam c.pu.le) ℓ' := by
        have hn := ptQ_le_normalizer_vv h464 h465 h466a c hX hXℓ' hAℓ' hyA
        have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ hv ((Subgroup.mem_normalizer_iff.mp hn _).mp
          (Subgroup.inv_mem _ hv))
      exact vv_comm c.pu hb hℓ' (hV ▸ hu) hvy
    · have hr : y ∈ ptQ (puAmalgam c.pu.le) X (Usup _ X ℓ ⊓ Usup _ X ℓ') := by
        rwa [← hAmeet hXℓ hXℓ' he hAℓ hAℓ']
      exact commute_vv_commutator_vv_ptQ' h464 h465 h466a c hX hXℓ hXℓ' he hu hv hr
  set v₂ := yB * w₀⁻¹ * yB⁻¹ with hv₂def
  have hv₂ : v₂ ∈ Vv (puAmalgam c.pu.le) μ' := by
    rw [hVμ']; exact ⟨w₀⁻¹, Subgroup.inv_mem _ hw₀, rfl⟩
  have he : ⁅⁅w₀, yB⁆, y⁆ = ⁅v₂, y⁆ * ⁅w₀, y⁆ := by
    have e1 : ⁅⁅w₀, yB⁆, y⁆ = w₀ * ⁅v₂, y⁆ * w₀⁻¹ * ⁅w₀, y⁆ := by
      simp only [hv₂def, commutatorElement_def]; group
    rw [e1, hcomm hXμ hXμ' hAμ hAμ' w₀ hw₀ v₂ hv₂, mul_assoc _ w₀ w₀⁻¹, mul_inv_cancel,
      mul_one]
  have hcc : ∀ t ∈ Vv (puAmalgam c.pu.le) k, t * ⁅⁅w₀, yB⁆, y⁆ = ⁅⁅w₀, yB⁆, y⁆ * t := by
    intro t ht
    have h1 := hcomm hXk hXμ' hAk hAμ' t ht v₂ hv₂
    have h2 := hcomm hXk hXμ hAk hAμ t ht w₀ hw₀
    rw [he]
    calc t * (⁅v₂, y⁆ * ⁅w₀, y⁆) = (t * ⁅v₂, y⁆) * ⁅w₀, y⁆ := by group
      _ = (⁅v₂, y⁆ * t) * ⁅w₀, y⁆ := by rw [h1]
      _ = ⁅v₂, y⁆ * (t * ⁅w₀, y⁆) := by group
      _ = ⁅v₂, y⁆ * (⁅w₀, y⁆ * t) := by rw [h2]
      _ = ⁅v₂, y⁆ * ⁅w₀, y⁆ * t := by group
  have hw₀T : w₀ ∈ Qv (puAmalgam c.pu.le) β :=
    vv_le_qv_of_adj_isMVtx c hX hXβ (I466b.vv_le_vv_of_adj c.pu hX hXμ hw₀)
  have hq : ⁅w₀, yB⁆ ∈ Qv (puAmalgam c.pu.le) Y :=
    burnsideD468_commutator_mem_qv h464 h465 h466a c hY hYβ hw₀T hyBT
  have hcZ : ⁅⁅w₀, yB⁆, y⁆ ∈ ZM (puAmalgam c.pu.le) Y := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ ((h465 G M T L F φ c Y β hY hYβ).2.2
      (Subgroup.commutator_mem_commutator hyV hq))
  have hkβ : (puAmalgam c.pu.le).treeGraph.dist k β ≤ 2 := by
    have h1 := dist_triangle (puAmalgam c.pu.le) k X β
    rw [tdist_comm (puAmalgam c.pu.le) k X, dist_eq_one_of_adj _ hXk,
      dist_eq_one_of_adj _ hXβ] at h1
    exact h1
  have hcβ : ⁅⁅w₀, yB⁆, y⁆ ∈ ZH (puAmalgam c.pu.le) β := by
    by_contra hn
    apply hkY
    intro t ht
    exact mem_qv_of_commute c.pu c.via h464' hsq h466 hY hYβ hcZ hn
      (vv_le_qv_of_dist_le_two hb4 hk hkβ ht) (hcc t ht)
  have hwμ : ⁅w₀, y⁆ ∈ Vv (puAmalgam c.pu.le) μ := by
    have hn := ptQ_le_normalizer_vv h464 h465 h466a c hX hXμ hAμ hyA
    have e : ⁅w₀, y⁆ = w₀ * (y * w₀⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hw₀ ((Subgroup.mem_normalizer_iff.mp hn _).mp
      (Subgroup.inv_mem _ hw₀))
  have hwμ' : ⁅v₂, y⁆⁻¹ ∈ Vv (puAmalgam c.pu.le) μ' := by
    refine Subgroup.inv_mem _ ?_
    have hn := ptQ_le_normalizer_vv h464 h465 h466a c hX hXμ' hAμ' hyA
    have e : ⁅v₂, y⁆ = v₂ * (y * v₂⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hv₂ ((Subgroup.mem_normalizer_iff.mp hn _).mp
      (Subgroup.inv_mem _ hv₂))
  have hcB : ⁅⁅w₀, yB⁆, y⁆ ∈ bzero c X := zm_le_bzero c hX (zh_le_zm _ hXβ hcβ)
  apply hbad
  refine mem_bzero_of_mem_vv_mul' h464 h465 c hX hXμ hXμ' (Ne.symm hμ'μ) hwμ hwμ' hcB
    (by rw [he]; group) fun ℓ hXℓ hℓ v hv => ?_
  rw [← hAmeet hXμ hXμ' (Ne.symm hμ'μ) hAμ hAμ'] at hℓ
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm hXℓ hXμ hℓ hAμ v hv w₀ hw₀).symm]
  exact Subgroup.one_mem _

theorem burnsideD468_false_of_not_s468At (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α₀ β₀ : Vtx (puAmalgam c.pu.le)} (hα₀ : IsMVtx (puAmalgam c.pu.le) α₀)
    (hα₀β₀ : (puAmalgam c.pu.le).treeGraph.Adj α₀ β₀)
    (hbad : ¬ S468At (puAmalgam c.pu.le) α₀ β₀) : False := by
  have hb4 := c.b4
  obtain ⟨α, α', hc⟩ := exists_isCritical _ c.pu.hyp20
  have hα := hc.1
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβx : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hx : IsMVtx (puAmalgam c.pu.le) (geo _ α α' 2) := isMVtx_geo_two' hb4 hc
  have hα' : IsMVtx (puAmalgam c.pu.le) α' := hc.isMVtx_right _ c.pu.hyp20
  have hcrev := ms22_iii _ c.pu.hyp20 c.pu.critDist_pos c.pu.centHyp hc
  obtain ⟨z, hzZ, hzα⟩ := SetLike.not_le_iff_exists.mp hcrev.2.2
  have hzV : z ∈ Vv (puAmalgam c.pu.le) (geo _ α α' 2) :=
    zm_le_vv_of_dist_le_two hα' (by rw [dist_geo_crit_right hb4 hc (by omega)]) hzZ
  have hzT : z ∈ Qv (puAmalgam c.pu.le) (geo _ α α' 1) :=
    vv_le_qv_of_adj_isMVtx c hx hβx.symm hzV
  obtain ⟨b, hb, hzb⟩ := burnsideD468_exists_isPtOn_mem_ptQ h464 h465 h466a c hα hαβ hzT hzα
  obtain ⟨μ, hαμ, hbμ, w, hw, hwz⟩ :=
    burnsideD468_exists_bad_line h464 h465 h466a c hbad hα₀ hα₀β₀ hα hαβ hb hzT hzb hzα
  by_cases hwx : w ∈ Qv (puAmalgam c.pu.le) (geo _ α α' 2)
  · exact hwz (burnsideD468_commutator_mem_bzero_of_mem_qv h464 h465 h466a c hα hαβ hx hβx hb
      hαμ hbμ hw hwx hzV hzb)
  · exact hwz (burnsideD468_commutator_mem_bzero_of_not_le h464 h465 h466a c hα hαβ hx hβx hb
      hαμ hbμ (fun h => hwx (h hw)) hαμ hbμ hw hzV hzb)

theorem burnsideD468_s468At_of_items (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α β : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) : S468At (puAmalgam c.pu.le) α β := by
  by_contra hbad
  exact burnsideD468_false_of_not_s468At h464 h465 h466a c hα hαβ hbad

theorem burnsideD468_s468DegN_of_items (h464 : I464) (h465 : I465) (h466a : I466a) :
    S46R.S468DegN :=
  fun _ _ _ _ _ _ _ _ _ _ c _ _ hα hαβ _ _ => burnsideD468_s468At_of_items h464 h465 h466a c hα hαβ

end CFSG.Yardstones.M71b2fd3d34b9
