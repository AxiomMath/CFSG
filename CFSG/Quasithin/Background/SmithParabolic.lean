module

public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.Quasithin.SmithCurtis

section

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

theorem exists_fixed_mem_of_stable {p : ℕ} [Fact p.Prime] [CharP k p]
    (ρ : Representation k G V) {S : Subgroup G} [Finite S] (hS : IsPGroup p S)
    {W : Submodule k V} (hW : ∀ g ∈ S, ∀ w ∈ W, ρ g w ∈ W) (hne : W ≠ ⊥) :
    ∃ x ∈ W, x ≠ 0 ∧ x ∈ fixSub ρ S := by
  have htop : IsPGroup p (⊤ : Subgroup S) := hS.of_equiv Subgroup.topEquiv.symm
  have hW' : ∀ g : S, ∀ w ∈ W, (ρ.comp S.subtype) g w ∈ W :=
    fun g w hw => hW g.1 g.2 w hw
  obtain ⟨x, hxW, hx0, hxfix⟩ :=
    exists_fixed_mem (ρ := ρ.comp S.subtype) htop hW' hne
  refine ⟨x, hxW, hx0, fun g hg => ?_⟩
  simpa using hxfix ⟨g, hg⟩ (Subgroup.mem_top _)

theorem mem_fixSub_sup (ρ : Representation k G V) {S T : Subgroup G} {v : V}
    (hS : v ∈ fixSub ρ S) (hT : v ∈ fixSub ρ T) : v ∈ fixSub ρ (S ⊔ T) := by
  rw [mem_fixSub] at hS hT ⊢
  intro g hg
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hS x hx
    · exact hT x hx
  | one => rw [map_one, Module.End.one_apply]
  | mul x y _ _ hx hy => rw [map_mul, Module.End.mul_apply, hy, hx]
  | inv x _ hx =>
    have h := act_mul ρ x⁻¹ x v
    rw [hx, inv_mul_cancel, map_one, Module.End.one_apply] at h
    exact h

theorem eq_zero_of_mem_augSub_of_fixed (ρ : Representation k G V) {S : Subgroup G}
    {f : Module.Dual k V} (hf : ∀ g ∈ S, ρ.dual g f = f) {z : V}
    (hz : z ∈ augSub ρ S) : f z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, hg, v, rfl⟩ := hz
    have h := congrArg (fun φ : Module.Dual k V => φ v) (hf g⁻¹ (S.inv_mem hg))
    simp only [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
      LinearMap.coe_comp, Function.comp_apply] at h
    rw [map_sub, h, sub_self]
  | zero => exact map_zero f
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

end

namespace CurtisDatum

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p)
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem exists_sub_smul_mem_augL [Finite G] (ρ : Representation k G V)
    {y : V} {χ : G → k} {μ : B → k} (hy : y ∈ D.fixU ρ)
    (hχ : ∀ h ∈ D.H, ρ h y = χ h • y) (hμ : ∀ s, D.heckeT ρ s y = μ s • y)
    {v : V} (hv : v ∈ orbitSpan ρ y) :
    ∃ c : k, v - c • y ∈ augSub ρ D.L := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, rfl⟩ := hv
    exact ⟨D.sph χ μ g, D.act_sub_sph_mem_augL ρ hy hχ hμ g⟩
  | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc⟩ := ha
    obtain ⟨c', hc'⟩ := hb
    refine ⟨c + c', ?_⟩
    have e : a + b - (c + c') • y = (a - c • y) + (b - c' • y) := by rw [add_smul]; abel
    rw [e]
    exact add_mem hc hc'
  | smul a v _ hv =>
    obtain ⟨c, hc⟩ := hv
    refine ⟨a * c, ?_⟩
    rw [mul_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hc

theorem mem_of_fixSub_of_stable [Finite G] [Fact p.Prime] [CharP k p]
    (ρ : Representation k G V) {N P : Subgroup G} (hU : D.U ≤ N ⊔ (D.U ⊓ P))
    (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    {Z : Submodule k V} (hZ : Z ≤ fixSub ρ N) (hZP : ∀ m ∈ P, ∀ x ∈ Z, ρ m x ∈ Z)
    (hne : Z ≠ ⊥) : y ∈ Z := by
  have hS : IsPGroup p (D.U ⊓ P : Subgroup G) := D.isPGroup_U.to_le inf_le_left
  have hstab : ∀ g ∈ (D.U ⊓ P : Subgroup G), ∀ w ∈ Z, ρ g w ∈ Z :=
    fun g hg w hw => hZP g ((inf_le_right : D.U ⊓ P ≤ P) hg) w hw
  obtain ⟨x, hxZ, hx0, hxS⟩ := exists_fixed_mem_of_stable ρ hS hstab hne
  have hxN : x ∈ fixSub ρ N := hZ hxZ
  have hxU : x ∈ D.fixU ρ := fixSub_anti ρ hU (mem_fixSub_sup ρ hxN hxS)
  have hxspan : x ∈ Submodule.span k {y} := by
    rw [← D.fixU_eq_span (ρ := ρ) hρ ht]
    exact hxU
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxspan
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact hx0 hc.symm
  have hy : y = c⁻¹ • x := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hy]
  exact Submodule.smul_mem _ _ hxZ

theorem act_mem_orbit_sup_augSub (ρ : Representation k G V) {N' P : Subgroup G}
    (hN' : ∀ m ∈ P, ∀ x ∈ N', m * x * m⁻¹ ∈ N') (hL : D.L ≤ N' ⊔ P) {y : V}
    {g : G} (hg : g ∈ D.L) :
    ∀ w ∈ Submodule.span k (Set.range fun m : P => ρ m y) ⊔ augSub ρ N',
      ρ g w ∈ Submodule.span k (Set.range fun m : P => ρ m y) ⊔ augSub ρ N' := by
  classical
  let O : Submodule k V := Submodule.span k (Set.range fun m : P => ρ m y)
  let W : Submodule k V := O ⊔ augSub ρ N'
  have hOP : ∀ m ∈ P, ∀ a ∈ O, ρ m a ∈ O := by
    intro m hm a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨q, rfl⟩ := ha
      exact Submodule.subset_span ⟨⟨m * q, P.mul_mem hm q.2⟩, (act_mul ρ m q y).symm⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hAP : ∀ m ∈ P, ∀ a ∈ augSub ρ N', ρ m a ∈ augSub ρ N' :=
    fun m hm a ha => act_mem_augSub ρ (hN' m hm) ha
  have hWP : ∀ m ∈ P, ∀ w ∈ W, ρ m w ∈ W := by
    intro m hm w hw
    have hw' : w ∈ O ⊔ augSub ρ N' := hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw'
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (hOP m hm a ha))
      (Submodule.mem_sup_right (hAP m hm b hb))
  have hWN' : ∀ n ∈ N', ∀ w ∈ W, ρ n w ∈ W := by
    intro n hn w hw
    have hw' : w ∈ O ⊔ augSub ρ N' := hw
    have e : ρ n w = w + (ρ n w - w) := by abel
    rw [e]
    exact add_mem hw' (Submodule.mem_sup_right (sub_mem_augSub ρ hn w))
  let K : Subgroup G :=
    { carrier := {g | (∀ w ∈ W, ρ g w ∈ W) ∧ (∀ w ∈ W, ρ g⁻¹ w ∈ W)}
      one_mem' := ⟨fun w hw => by rw [map_one, Module.End.one_apply]; exact hw,
        fun w hw => by rw [inv_one, map_one, Module.End.one_apply]; exact hw⟩
      mul_mem' := fun {g h} hg hh =>
        ⟨fun w hw => by
          rw [map_mul, Module.End.mul_apply]
          exact hg.1 _ (hh.1 w hw),
         fun w hw => by
          rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          exact hh.2 _ (hg.2 w hw)⟩
      inv_mem' := fun {g} hg =>
        ⟨fun w hw => hg.2 w hw, fun w hw => by simpa using hg.1 w hw⟩ }
  have hN'K : N' ≤ K := by
    intro n hn
    exact ⟨fun w hw => hWN' n hn w hw,
      fun w hw => hWN' n⁻¹ (N'.inv_mem hn) w hw⟩
  have hPK : P ≤ K := by
    intro m hm
    exact ⟨fun w hw => hWP m hm w hw, fun w hw => hWP m⁻¹ (P.inv_mem hm) w hw⟩
  have hLK : D.L ≤ K := hL.trans (sup_le hN'K hPK)
  exact (hLK hg).1

theorem orbit_sup_augSub_eq_top [Finite G] [Fact p.Prime] [CharP k p]
    (ρ : Representation k G V) (hρ : IsSimpleRep ρ) {N' P : Subgroup G}
    (hN' : ∀ m ∈ P, ∀ x ∈ N', m * x * m⁻¹ ∈ N') (hL : D.L ≤ N' ⊔ P)
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) :
    Submodule.span k (Set.range fun m : P => ρ m y) ⊔ augSub ρ N' = ⊤ := by
  classical
  let W : Submodule k V := Submodule.span k (Set.range fun m : P => ρ m y) ⊔ augSub ρ N'
  have hWL : ∀ g ∈ D.L, ∀ w ∈ W, ρ g w ∈ W :=
    fun g hg w hw => D.act_mem_orbit_sup_augSub ρ hN' hL hg w hw
  by_contra htop
  have hann : W.dualAnnihilator ≠ ⊥ := by
    rw [ne_eq, Submodule.dualAnnihilator_eq_bot_iff]
    exact htop
  have hannStab : ∀ g ∈ D.L, ∀ f ∈ W.dualAnnihilator,
      ρ.dual g f ∈ W.dualAnnihilator := by
    intro g hg f hf
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro w hw
    have h1 : (ρ.dual g f) w = f (ρ g⁻¹ w) := by
      simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.coe_comp,
        Function.comp_apply]
    rw [h1]
    exact hf _ (hWL g⁻¹ (D.L.inv_mem hg) w hw)
  obtain ⟨f, hfann, hf0, hffix⟩ :=
    exists_fixed_mem_of_stable ρ.dual D.isPGroup_L hannStab hann
  have hfaug : ∀ z ∈ augSub ρ D.L, f z = 0 :=
    fun z hz => eq_zero_of_mem_augSub_of_fixed ρ hffix hz
  have hfy : f y = 0 := by
    have hyO : y ∈ Submodule.span k (Set.range fun m : P => ρ m y) :=
      Submodule.subset_span ⟨1, by simp⟩
    exact (Submodule.mem_dualAnnihilator f).mp hfann y (Submodule.mem_sup_left hyO)
  apply hf0
  ext v
  have hv : v ∈ orbitSpan ρ y := by
    rw [orbitSpan_eq_top hρ ht.2.1]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := D.exists_sub_smul_mem_augL ρ ht.1 ht.2.2.1 ht.2.2.2 hv
  have h0 := hfaug (v - c • y) hc
  rwa [map_sub, map_smul, hfy, smul_zero, sub_zero] at h0

theorem fixSub_inf_augSub_eq_bot [Finite G] [Fact p.Prime] [CharP k p]
    (ρ : Representation k G V) (hρ : IsSimpleRep ρ) {N N' P : Subgroup G}
    (hN : ∀ m ∈ P, ∀ x ∈ N, m * x * m⁻¹ ∈ N)
    (hN' : ∀ m ∈ P, ∀ x ∈ N', m * x * m⁻¹ ∈ N')
    (hN'L : N' ≤ D.L) (hU : D.U ≤ N ⊔ (D.U ⊓ P))
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) :
    fixSub ρ N ⊓ augSub ρ N' = ⊥ := by
  by_contra hne
  have hZP : ∀ m ∈ P, ∀ x ∈ fixSub ρ N ⊓ augSub ρ N',
      ρ m x ∈ fixSub ρ N ⊓ augSub ρ N' := by
    intro m hm x hx
    obtain ⟨hxN, hxA⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨act_mem_fixSub ρ ?_ hxN,
      act_mem_augSub ρ (hN' m hm) hxA⟩
    intro s hs
    have h := hN m⁻¹ (P.inv_mem hm) s hs
    simpa using h
  have hyZ : y ∈ fixSub ρ N ⊓ augSub ρ N' :=
    D.mem_of_fixSub_of_stable (ρ := ρ) hU hρ ht inf_le_left hZP hne
  have hyA : y ∈ augSub ρ D.L := augSub_mono ρ hN'L hyZ.2
  exfalso
  exact ht.2.1 (D.fixU_inf_augL (ρ := ρ) hρ ht.1 hyA)

theorem eq_bot_or_fixSub_le [Finite G] [Finite W] [Fact p.Prime] [CharP k p]
    (hsplit : SplitOver k D.H) {ρ : Representation k G V} (hρ : IsSimpleRep ρ)
    {N N' P : Subgroup G}
    (hN : ∀ m ∈ P, ∀ x ∈ N, m * x * m⁻¹ ∈ N) (hN' : ∀ m ∈ P, ∀ x ∈ N', m * x * m⁻¹ ∈ N')
    (hN'L : N' ≤ D.L) (hU : D.U ≤ N ⊔ (D.U ⊓ P)) (hL : D.L ≤ N' ⊔ P)
    {X : Submodule k V} (hX : X ≤ fixSub ρ N) (hXP : ∀ m ∈ P, ∀ x ∈ X, ρ m x ∈ X) :
    X = ⊥ ∨ fixSub ρ N ≤ X := by
  obtain ⟨y, χ, μ, ht⟩ := D.exists_isCurtisType (ρ := ρ) hsplit hρ
  by_cases hX0 : X = ⊥
  · exact Or.inl hX0
  · right
    have hyX : y ∈ X :=
      D.mem_of_fixSub_of_stable (ρ := ρ) hU hρ ht hX hXP hX0
    have hOX : Submodule.span k (Set.range fun m : P => ρ m y) ≤ X := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact hXP m m.2 y hyX
    have hbot := D.fixSub_inf_augSub_eq_bot (ρ := ρ) hρ hN hN' hN'L hU ht
    intro x hx
    have hxW : x ∈ Submodule.span k (Set.range fun m : P => ρ m y) ⊔ augSub ρ N' := by
      rw [D.orbit_sup_augSub_eq_top (ρ := ρ) hρ hN' hL ht]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxW
    have haX : a ∈ X := hOX ha
    have hbFix : b ∈ fixSub ρ N := by
      have hsub : x - a ∈ fixSub ρ N := Submodule.sub_mem _ hx (hX haX)
      have hba : x - a = b := by rw [← hab]; abel
      rwa [hba] at hsub
    have hbBot : b = 0 := by
      have hbinf : b ∈ fixSub ρ N ⊓ augSub ρ N' := ⟨hbFix, hb⟩
      rw [hbot] at hbinf
      exact (Submodule.mem_bot _).mp hbinf
    have hxa : x = a := by rw [← hab, hbBot, add_zero]
    rw [hxa]
    exact haX

end CurtisDatum

end CFSG.Quasithin.SmithCurtis
