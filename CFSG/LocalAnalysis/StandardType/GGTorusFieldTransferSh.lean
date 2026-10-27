module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreLine
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTorusNoLineSh (p r : ℕ) (R : Type) [Group R] (I Sh : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ((∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ Sh, ∀ l : L', φ (ψ l) = ψ (a₀ l)) ∨
            ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)

@[expose] def GGFixNotCycOn (p : ℕ) {R : Type} [Group R] (I : Set (MulAut R)) (x : MulAut R)
    {R₀ : Type} [Group R₀] (θ₀ : ggFixDer x ≃* R₀) (Sh : Set (MulAut R₀)) : Prop :=
  ∀ φ ∈ I, ∀ hφ : φ * x = x * φ, ∀ φ₀ ∈ Sh,
    (∀ (g : R) (hg : g ∈ ggFixDer x), θ₀ ⟨φ g, ggFixDer_map_mem hφ hg⟩ = φ₀ (θ₀ ⟨g, hg⟩)) →
      ¬ GGFixCompCyclic p φ

@[expose] def GGFixDataSh (p r : ℕ) {R : Type} [Group R] (I : Set (MulAut R)) (x : MulAut R) : Prop :=
  ∃ (R₀ : Type) (_ : Group R₀) (I₀ Sh : Set (MulAut R₀)) (θ₀ : ggFixDer x ≃* R₀),
    IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ GGFixGeom I x I₀ θ₀ ∧ GGTorusLift p r R₀ ∧
      GGTorusNoLineSh p r R₀ I₀ Sh ∧ GGFixNotCycOn p I x θ₀ Sh

theorem exists_isPGroup_le_of_le_map_prime {p : ℕ} (hp : p.Prime) {L' R : Type} [Group L'] [Finite L']
    [Group R] (ψ : L' →* R) {X : Subgroup L'} {E : Subgroup R} (hE : E ≤ X.map ψ)
    (hEp : IsPGroup p E) : ∃ P : Subgroup L', P ≤ X ∧ IsPGroup p P ∧ P.map ψ = E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Y : Subgroup L' := X ⊓ E.comap ψ
  have hYmap : Y.map ψ = E := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_right
    · rintro e he
      obtain ⟨x, hx, rfl⟩ := hE he
      exact ⟨x, ⟨hx, he⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow p ↥Y) := Sylow.nonempty
  refine ⟨(S : Subgroup ↥Y).map Y.subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le (H := Y) (S : Subgroup ↥Y)).trans inf_le_left
  · exact (S.isPGroup').map Y.subtype
  · let f : ↥Y →* ↥(Y.map ψ) := ψ.subgroupMap Y
    have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective ψ Y
    have hEp' : IsPGroup p (Y.map ψ) := by
      rw [hYmap]
      exact hEp
    have htop : IsPGroup p (⊤ : Subgroup ↥(Y.map ψ)) := hEp'.to_subgroup ⊤
    have hSmap : (S : Subgroup ↥Y).map f = ⊤ := by
      have h := (S.mapSurjective hf).is_maximal' (Q := ⊤) htop le_top
      rw [Sylow.coe_mapSurjective] at h
      exact h.symm
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap]
      have hxY : x ∈ Y := Subgroup.map_subtype_le (H := Y) (S : Subgroup ↥Y) hx
      rw [← hYmap]
      exact ⟨x, hxY, rfl⟩
    · intro e he
      have heY : e ∈ Y.map ψ := hYmap.symm ▸ he
      obtain ⟨y, hy, rfl⟩ := heY
      have hmem : (⟨ψ y, ⟨y, hy, rfl⟩⟩ : ↥(Y.map ψ)) ∈ (S : Subgroup ↥Y).map f := by
        rw [hSmap]
        exact Subgroup.mem_top _
      obtain ⟨s, hs, hsf⟩ := hmem
      refine ⟨(s : L'), ⟨s, hs, rfl⟩, ?_⟩
      have hval : (f s : R) = ψ y := congrArg Subtype.val hsf
      simpa [f] using hval

private theorem ggShAux_isCyclic_map_of_isCyclic {L' R : Type} [Group L'] [Group R]
    (P : Subgroup L') (hP : IsCyclic P) (ψ : L' →* R) : IsCyclic (P.map ψ) := by
  haveI : IsCyclic P := hP
  exact isCyclic_of_surjective (ψ.subgroupMap P) (MonoidHom.subgroupMap_surjective ψ P)

private theorem ggShAux_exists_lift_pgroup_other {p : ℕ} {L' R : Type} [Group L'] [Finite L']
    [Group R] {ψ : L' →* R} (hp : p.Prime) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'} {ab : MulAut R}
    (hc : ∀ l, ab (ψ l) = ψ (a l)) {J₁ : Subgroup L'} (hJ₁ : IsComponentOf J₁ (ggFix a))
    {Pb : Subgroup R} (hPb : IsPGroup p Pb)
    (hle : Pb ≤ ⨆ (B : Subgroup R) (_ : IsComponentOf B (ggFix ab) ∧ B ≠ J₁.map ψ ∧
      p ∣ Nat.card B), B) :
    ∃ P : Subgroup L', IsPGroup p P ∧ P.map ψ = Pb ∧
      P ≤ ⨆ (J₂ : Subgroup L') (_ : IsComponentOf J₂ (ggFix a) ∧ J₂ ≠ J₁ ∧ p ∣ Nat.card J₂), J₂ := by
  classical
  let X : Subgroup L' := ⨆ (J₂ : Subgroup L')
    (_ : IsComponentOf J₂ (ggFix a) ∧ J₂ ≠ J₁ ∧ p ∣ Nat.card J₂), J₂
  have hPbX : Pb ≤ X.map ψ := by
    refine hle.trans (iSup_le fun B => iSup_le fun hB => ?_)
    obtain ⟨hBc, hBne, hB3⟩ := hB
    let J₂ : Subgroup L' := ⁅B.comap ψ, B.comap ψ⁆
    obtain ⟨hJ₂c, hJ₂map⟩ :=
      CFSG.StandardType.USixTwo.isComponentOf_lift_fix hψ hker hc hBc
    have hJ₂map' : J₂.map ψ = B := hJ₂map
    have hJ₂ne : J₂ ≠ J₁ := by
      intro heq
      apply hBne
      rw [← hJ₂map', heq]
    have hJ₂p : p ∣ Nat.card J₂ := by
      have hp' : p ∣ Nat.card (J₂.map ψ) := by
        rw [hJ₂map']
        exact hB3
      exact hp'.trans (Subgroup.card_map_dvd J₂ ψ)
    rw [← hJ₂map']
    exact Subgroup.map_mono (le_iSup₂ (f := fun J₂ (_ : IsComponentOf J₂ (ggFix a) ∧
      J₂ ≠ J₁ ∧ p ∣ Nat.card J₂) => J₂) J₂ ⟨hJ₂c, hJ₂ne, hJ₂p⟩)
  obtain ⟨P, hPX, hPp, hPmap⟩ := exists_isPGroup_le_of_le_map_prime hp ψ hPbX hPb
  exact ⟨P, hPp, hPmap, hPX⟩

theorem ggFixCompCyclic_map_prime {p : ℕ} (hp : p.Prime) {L' R : Type} [Group L'] [Finite L']
    [Group R] {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {ab : MulAut R} (hc : ∀ l, ab (ψ l) = ψ (a l))
    (h : GGFixCompCyclic p a) : GGFixCompCyclic p ab := by
  unfold GGFixCompCyclic at h ⊢
  obtain ⟨J₁, hJ₁, hcyc⟩ := h
  refine ⟨J₁.map ψ, CFSG.StandardType.USixTwo.isComponentOf_map_fix hψ hker hc hJ₁, ?_⟩
  intro Pb hPbp hPble
  obtain ⟨P, hPp, hPmap, hPle⟩ :=
    ggShAux_exists_lift_pgroup_other hp hψ hker hc hJ₁ hPbp hPble
  have hPcyc : IsCyclic P := hcyc P hPp hPle
  rw [← hPmap]
  exact ggShAux_isCyclic_map_of_isCyclic P hPcyc ψ

theorem ggTorusLiftFix_of_fixDataSh {p r : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataSh p r I x) :
    GGTorusLiftFix p r R I F := by
  intro L' _ _ ψ hψ hker hperf f hfp hind hnot
  obtain ⟨x, hx, hxψ⟩ := hind
  have hxI : x ∉ I := fun h => hnot ⟨x, h, hxψ⟩
  have hxp : x ^ p = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [ggInduced_pow ψ hxψ p l, hfp]
    rfl
  obtain ⟨R₀, _, I₀, -, θ₀, hs, hna, -, hlift, -⟩ := hfix x hx hxI hxp
  obtain ⟨ψ'', -, hsurj, hker', hkerc, hperf''⟩ :=
    ggSubfieldCore ψ hψ hker (ggFixDer x) (ggFixDer_perfect θ₀ hs hna) θ₀
  have hfH : ∀ l ∈ ggCore ψ (ggFixDer x), f l = l := fun l hl =>
    ggFixes_core ψ hker f x (fun l => (hxψ l).symm) ((ggFixDer x).comap ψ)
      (fun l hl => ggFixDer_le_ggFixSub x hl) hl
  exact ggTorusLift_pushforward ψ (ggCore ψ (ggFixDer x)) ψ'' hsurj hkerc hperf'' hker' hlift f hfH

theorem ggTorusNoLineFieldComp_of_fixDataSh {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r) {R : Type}
    [Group R] {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hin : GGTorusNoLineComp p r R I)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataSh p r I x) :
    GGTorusNoLineFieldComp p r R I F := by
  intro L' _ _ ψ hψ hker hperf A hAe hAind hcard1 hcard3 hsc
  obtain ⟨J, S, hJI, hJS, hN, hgen, hS⟩ := hcyc
  have hIJ : ∀ φ : MulAut R, φ ∈ I ↔ φ ∈ J := fun φ => by rw [← hJI]; rfl
  obtain ⟨Ind, hInd⟩ := ggInducedHom_exists ψ hψ A (fun a ha => by
    obtain ⟨φ, -, h⟩ := hAind a ha
    exact ⟨φ, h⟩)
  have hIndcl : ∀ a : A, Ind a ∈ Subgroup.closure (I ∪ F) := by
    intro a
    obtain ⟨φ, hφ, h⟩ := hAind a a.2
    rw [ggInduced_unique hψ (hInd a) h]
    exact hφ
  have hexp : ∀ u ∈ A, u ^ p = 1 := hAe.2
  have hIndp : ∀ a : A, Ind a ^ p = 1 := by
    intro a
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hexp a a.2)
    rw [this, map_one]
  have hIndS : ∀ a : A, Ind a ∈ S := fun a => hS _ (hIndcl a) ⟨1, by simpa using hIndp a⟩
  let A₀ : Subgroup (MulAut L') := (J.comap Ind).map A.subtype
  have hA₀A : A₀ ≤ A := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hmem : ∀ a : A, (a : MulAut L') ∈ A₀ ↔ Ind a ∈ J := by
    intro a
    constructor
    · rintro ⟨a', ha', h⟩
      have : a' = a := Subtype.ext h
      subst this
      exact ha'
    · intro h
      exact ⟨a, h, rfl⟩
  obtain ⟨hcardle, hgenA⟩ := ggCyclicSplit hp hA₀A hexp Ind hN hgen hIndS hmem
  by_cases hAA₀ : A ≤ A₀
  · have hind : ∀ a ∈ A, ∃ φ ∈ I, ∀ l, φ (ψ l) = ψ (a l) := by
      intro a ha
      exact ⟨Ind ⟨a, ha⟩, (hIJ _).mpr ((hmem ⟨a, ha⟩).mp (hAA₀ ha)), hInd ⟨a, ha⟩⟩
    have hc1 : p ^ r ≤ Nat.card A :=
      (Nat.pow_le_pow_right hp.pos (Nat.le_succ r)).trans hcard1
    obtain ⟨W, h1, h2⟩ := hin L' ψ hψ hker hperf A hAe hind hc1 hcard3 hsc
    exact ⟨W, h1, fun hN' a₀ ha₀ hne _ hcl => h2 hN' a₀ ha₀ hne hcl⟩
  · obtain ⟨b, hbA, hbA₀⟩ := SetLike.not_le_iff_exists.mp hAA₀
    set x : MulAut R := Ind ⟨b, hbA⟩ with hx
    have hxcl : x ∈ Subgroup.closure (I ∪ F) := hIndcl _
    have hxI : x ∉ I := fun h => hbA₀ ((hmem ⟨b, hbA⟩).mpr ((hIJ _).mp h))
    obtain ⟨R₀, _, I₀, Sh, θ₀, hs₀, hna₀, hgeom, -, hline₀, hX⟩ :=
      hfix x hxcl hxI (hIndp _)
    have hK : ⁅ggFixDer x, ggFixDer x⁆ = ggFixDer x := ggFixDer_perfect θ₀ hs₀ hna₀
    obtain ⟨ψ'', hψ''eq, hψ''s, hψ''i, hψ''kc, hψ''p⟩ :=
      ggSubfieldCore ψ hψ hker (ggFixDer x) hK θ₀
    have hmapK : (ggCore ψ (ggFixDer x)).map ψ = ggFixDer x :=
      (ggPerfectCore ψ hψ hker (ggFixDer x) hK).1
    have hHK : ∀ l ∈ ggCore ψ (ggFixDer x), ψ l ∈ ggFixDer x := fun l hl => by
      rw [← hmapK]
      exact Subgroup.mem_map_of_mem ψ hl
    have hcomm : ∀ a : A, Ind a * x = x * Ind a := by
      intro a
      rw [hx, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAe.comm a.2 hbA)
    have hstab : ∀ a ∈ A, ∀ l ∈ ggCore ψ (ggFixDer x), a l ∈ ggCore ψ (ggFixDer x) :=
      fun a ha l hl =>
        ggCore_stab ψ (ggFixDer x) a (Ind ⟨a, ha⟩) (hInd ⟨a, ha⟩)
          (fun g hg => ggFixDer_map_mem (hcomm ⟨a, ha⟩) hg) l hl
    have hbH : ∀ l ∈ ggCore ψ (ggFixDer x), b l = l := fun l hl =>
      mem_ggFixSub.mp (ggFixes_core ψ hker b x (fun l => (hInd ⟨b, hbA⟩ l).symm)
        ((ggFixDer x).comap ψ) (fun l hl => ggFixDer_le_ggFixSub x hl) hl)
    generalize ggCore ψ (ggFixDer x) = H at hmapK hHK hstab hbH ψ'' hψ''eq hψ''s hψ''i hψ''kc hψ''p
    obtain ⟨res, hres⟩ := ggAutRestrictHom H A₀ (fun a ha => hstab a (hA₀A ha))
    have hdec := ggTransfer_decomp (A := A) (A₀ := A₀) (H := H) hbH (hgenA b hbA hbA₀)
    have hcJ : ∀ c : A₀, Ind ⟨(c : MulAut L'), hA₀A c.2⟩ ∈ J := fun c => (hmem _).mp c.2
    have hinj : Function.Injective res := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have h1 : Ind ⟨(c : MulAut L'), hA₀A c.2⟩ = 1 := by
        refine hgeom.2 _ ((hIJ _).mpr (hcJ c)) (hcomm _) ?_
        intro g hg
        have hg' : g ∈ H.map ψ := by rw [hmapK]; exact hg
        obtain ⟨l, hl, rfl⟩ := hg'
        have e : ((res c ⟨l, hl⟩ : H) : L') = (c : MulAut L') l := hres c ⟨l, hl⟩
        rw [hc] at e
        rw [hInd _ l, ← e]
        rfl
      refine Subtype.ext (ggAut_eq_one_of_induced_one ψ hker hperf c fun l => ?_)
      rw [← hInd ⟨(c : MulAut L'), hA₀A c.2⟩ l, h1]
      rfl
    have hB₀ind : ∀ a ∈ res.range, ∃ φ₀ ∈ I₀, ∀ l : H, φ₀ (ψ'' l) = ψ'' (a l) := by
      rintro _ ⟨c, rfl⟩
      obtain ⟨φ₀, hφ₀, hφ₀eq⟩ := hgeom.1 (Ind ⟨(c : MulAut L'), hA₀A c.2⟩) ((hIJ _).mpr (hcJ c))
        (hcomm _)
      refine ⟨φ₀, hφ₀, fun l => ?_⟩
      rw [hψ''eq l (hHK l l.2), hψ''eq (res c l) (hHK _ (res c l).2), ← hφ₀eq (ψ l) (hHK l l.2)]
      congr 2
      rw [hInd _ l, hres c l]
    have hconj : ∀ n ∈ H, MulAut.conj n ∈ A → MulAut.conj n ∈ A₀ := by
      intro n _ hn
      have e : Ind ⟨MulAut.conj n, hn⟩ = MulAut.conj (ψ n) :=
        ggInduced_unique hψ (hInd _) (fun l => ggInduced_conj ψ n l)
      exact (hmem ⟨MulAut.conj n, hn⟩).mpr (by rw [e, ← hIJ]; exact hInn _)
    have hnorm : ∀ n ∈ H, ∀ a ∈ A₀, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A →
        MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A₀ := by
      intro n _ a ha hc
      have e : Ind ⟨MulAut.conj n * a * (MulAut.conj n)⁻¹, hc⟩ =
          MulAut.conj (ψ n) * Ind ⟨a, hA₀A ha⟩ * (MulAut.conj (ψ n))⁻¹ :=
        ggInduced_unique hψ (hInd _) (ggInduced_conj_mul_conj_inv ψ n (hInd ⟨a, hA₀A ha⟩))
      have hcn : MulAut.conj (ψ n) ∈ J := (hIJ _).mp (hInn _)
      refine (hmem ⟨_, hc⟩).mpr ?_
      rw [e]
      exact J.mul_mem (J.mul_mem hcn ((hmem ⟨a, hA₀A ha⟩).mp ha)) (J.inv_mem hcn)
    have hcardB₀ : Nat.card res.range = Nat.card A₀ :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have hsc₀ := ggTransfer_selfCent res hres hdec hsc hconj
    have hNr : p ^ r ≤ Nat.card res.range := by
      rw [hcardB₀]
      have h : p * p ^ r ≤ p * Nat.card A₀ :=
        calc p * p ^ r = p ^ r * p := mul_comm _ _
          _ = p ^ (r + 1) := (pow_succ p r).symm
          _ ≤ Nat.card A := hcard1
          _ ≤ p * Nat.card A₀ := hcardle
      exact Nat.le_of_mul_le_mul_left h hp.pos
    have hN3 : p ^ 3 ≤ Nat.card res.range := (Nat.pow_le_pow_right hp.pos hr).trans hNr
    obtain ⟨W₀, h1, h2⟩ := hline₀ H ψ'' hψ''s hψ''kc hψ''p res.range
      (ggIsElemAbelian_range hA₀A hAe res) hB₀ind hNr hN3 hsc₀
    refine ⟨Subtype.val '' W₀, ggTransfer_first res hres hdec h1, ?_⟩
    intro hN' a₀ ha₀ hne hind hcl
    have ha₀A₀ : a₀ ∈ A₀ := by
      obtain ⟨φ, hφ, h⟩ := hind
      have e := ggInduced_unique hψ (hInd ⟨a₀, ha₀⟩) h
      exact (hmem ⟨a₀, ha₀⟩).mpr (by rw [e]; exact (hIJ _).mp hφ)
    rcases ggTransfer_secondX res hres hinj hA₀A hnorm
        (Q := fun a => ∃ φ ∈ Sh, ∀ l : H, φ (ψ'' l) = ψ'' (a l)) h2 hN' a₀ ha₀A₀ hne with
      ⟨φ₀, hφ₀Sh, hφ₀⟩ | hmove
    ·
      exfalso
      set φ : MulAut R := Ind ⟨a₀, ha₀⟩ with hφdef
      have hφI : φ ∈ I := (hIJ _).mpr ((hmem ⟨a₀, ha₀⟩).mp ha₀A₀)
      have hφx : φ * x = x * φ := hcomm ⟨a₀, ha₀⟩
      have hrestr : ∀ (g : R) (hg : g ∈ ggFixDer x),
          θ₀ ⟨φ g, ggFixDer_map_mem hφx hg⟩ = φ₀ (θ₀ ⟨g, hg⟩) := by
        intro g hg
        have hg' : g ∈ H.map ψ := by rw [hmapK]; exact hg
        obtain ⟨l, hl, rfl⟩ := hg'
        have e1 : φ (ψ l) = ψ (a₀ l) := hInd ⟨a₀, ha₀⟩ l
        have e2 : ((res ⟨a₀, ha₀A₀⟩ ⟨l, hl⟩ : H) : L') = a₀ l := hres ⟨a₀, ha₀A₀⟩ ⟨l, hl⟩
        have e3 := hφ₀ ⟨l, hl⟩
        rw [hψ''eq ⟨l, hl⟩ (hHK l hl),
          hψ''eq (res ⟨a₀, ha₀A₀⟩ ⟨l, hl⟩) (hHK _ (res ⟨a₀, ha₀A₀⟩ ⟨l, hl⟩).2)] at e3
        rw [e3]
        congr 2
        rw [e2]
        exact e1
      exact (hX φ hφI hφx φ₀ hφ₀Sh hrestr)
        (ggFixCompCyclic_map_prime hp hψ hker (hInd ⟨a₀, ha₀⟩) hcl)
    · exact hmove

theorem ggTorusFieldTransferSh {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hin : GGTorusNoLineComp p r R I)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataSh p r I x) :
    GGTorusLiftFix p r R I F ∧ GGTorusNoLineFieldComp p r R I F :=
  ⟨ggTorusLiftFix_of_fixDataSh hfix,
    ggTorusNoLineFieldComp_of_fixDataSh hp hr hInn hin hcyc hfix⟩

theorem ggFixCompCyclic_conj {p : ℕ} {R : Type} [Group R] {φ : MulAut R} (u : MulAut R)
    (h : GGFixCompCyclic p φ) : GGFixCompCyclic p (u⁻¹ * φ * u) := by
  obtain ⟨J₁, hJ₁, hcyc⟩ := h
  have hmapmap : ∀ H : Subgroup R,
      (H.map (u⁻¹ : MulAut R).toMonoidHom).map (u : MulAut R).toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    have hcomp : (u : MulAut R).toMonoidHom.comp (u⁻¹ : MulAut R).toMonoidHom =
        MonoidHom.id R := by ext x; simp
    rw [hcomp, Subgroup.map_id]
  refine ⟨J₁.map (u⁻¹ : MulAut R).toMonoidHom, ?_, ?_⟩
  · rw [ggFix_conj_eq_map]
    exact ⟨Subgroup.map_mono hJ₁.1, IsSubnormal.map _ hJ₁.2.1,
      Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective J₁ _ (u⁻¹ : MulAut R).injective).symm hJ₁.2.2⟩
  · intro P hPp hPle
    have hle0 : P.map (u : MulAut R).toMonoidHom ≤
        (⨆ (J₂ : Subgroup R) (_ : IsComponentOf J₂ (ggFix (u⁻¹ * φ * u)) ∧
          J₂ ≠ J₁.map (u⁻¹ : MulAut R).toMonoidHom ∧ p ∣ Nat.card J₂), J₂).map
          (u : MulAut R).toMonoidHom := Subgroup.map_mono hPle
    simp only [Subgroup.map_iSup] at hle0
    have hle : P.map (u : MulAut R).toMonoidHom ≤
        ⨆ (K : Subgroup R) (_ : IsComponentOf K (ggFix φ) ∧ K ≠ J₁ ∧ p ∣ Nat.card K), K := by
      refine hle0.trans (iSup_le fun J₂ => iSup_le fun hJ₂ => ?_)
      obtain ⟨hJ₂c, hJ₂ne, hJ₂p⟩ := hJ₂
      rw [ggFix_conj_eq_map] at hJ₂c
      have hcomp : IsComponentOf (J₂.map (u : MulAut R).toMonoidHom) (ggFix φ) := by
        refine ⟨?_, ?_, ?_⟩
        · have h := Subgroup.map_mono hJ₂c.1 (f := (u : MulAut R).toMonoidHom)
          rwa [hmapmap (ggFix φ)] at h
        · have h := IsSubnormal.map (u : MulAut R).toMonoidHom hJ₂c.2.1
          rwa [hmapmap (ggFix φ)] at h
        · exact Assembly.IsQuasisimple.of_mulEquiv
            (Subgroup.equivMapOfInjective J₂ (u : MulAut R).toMonoidHom
              (u : MulAut R).injective).symm hJ₂c.2.2
      have hne : J₂.map (u : MulAut R).toMonoidHom ≠ J₁ := by
        intro hEq
        apply hJ₂ne
        have h1 : (J₂.map (u : MulAut R).toMonoidHom).map (u⁻¹ : MulAut R).toMonoidHom = J₂ := by
          rw [Subgroup.map_map]
          have hcomp : (u⁻¹ : MulAut R).toMonoidHom.comp (u : MulAut R).toMonoidHom =
              MonoidHom.id R := by ext x; simp
          rw [hcomp, Subgroup.map_id]
        have h2 := congrArg (fun K : Subgroup R => K.map (u⁻¹ : MulAut R).toMonoidHom) hEq
        rwa [h1] at h2
      have hpdiv : p ∣ Nat.card (J₂.map (u : MulAut R).toMonoidHom) := by
        have hcard : Nat.card J₂ = Nat.card (J₂.map (u : MulAut R).toMonoidHom) :=
          Nat.card_congr (Subgroup.equivMapOfInjective J₂ (u : MulAut R).toMonoidHom
            (u : MulAut R).injective).toEquiv
        rw [← hcard]
        exact hJ₂p
      exact le_iSup₂ (f := fun K (_ : IsComponentOf K (ggFix φ) ∧ K ≠ J₁ ∧ p ∣ Nat.card K) => K)
        (J₂.map (u : MulAut R).toMonoidHom) ⟨hcomp, hne, hpdiv⟩
    have hcyc' : IsCyclic (P.map (u : MulAut R).toMonoidHom) := hcyc _ (hPp.map _) hle
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective P (u : MulAut R).toMonoidHom
        (u : MulAut R).injective).symm).mp hcyc'

theorem ggFixDataSh_conj {p r : ℕ} {R : Type} [Group R] {J : Subgroup (MulAut R)} {f u : MulAut R}
    (hu : u ∈ J) (h : GGFixDataSh p r (J : Set (MulAut R)) f) :
    GGFixDataSh p r (J : Set (MulAut R)) (u * f * u⁻¹) := by
  obtain ⟨R₀, i₀, I₀, Sh, θ₀, hs, hna, hgeom, hlift, hline, hX⟩ := h
  let e : ggFixDer (u * f * u⁻¹) ≃* ggFixDer f :=
    { toFun := fun g => ⟨u⁻¹ (g : R), (ggFixDer_conj_mem f u (g : R)).1 g.2⟩
      invFun := fun k => ⟨u (k : R), by
        rw [ggFixDer_conj_mem]
        simpa using k.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp)
      map_mul' := fun g k => Subtype.ext (by simp) }
  have he : ∀ g : ggFixDer (u * f * u⁻¹), ((e g : ggFixDer f) : R) = u⁻¹ (g : R) :=
    fun _ => rfl
  have hres : ∀ (φ : MulAut R) (hφ : φ * (u * f * u⁻¹) = (u * f * u⁻¹) * φ) (g : R)
      (hg : g ∈ ggFixDer (u * f * u⁻¹)),
      (e.trans θ₀) ⟨φ g, ggFixDer_map_mem hφ hg⟩ =
        θ₀ ⟨(u⁻¹ * φ * u) (u⁻¹ g),
          ggFixDer_map_mem (ggConj_commute_line hφ) ((ggFixDer_conj_mem f u g).1 hg)⟩ := by
    intro φ hφ g hg
    rw [MulEquiv.trans_apply]
    congr 1
    apply Subtype.ext
    rw [he]
    simp only [MulAut.mul_apply, MulAut.apply_inv_self]
  have hres' : ∀ (g : R) (hg : g ∈ ggFixDer (u * f * u⁻¹)),
      (e.trans θ₀) ⟨g, hg⟩ = θ₀ ⟨u⁻¹ g, (ggFixDer_conj_mem f u g).1 hg⟩ := by
    intro g hg
    rw [MulEquiv.trans_apply]
    congr 1
  refine ⟨R₀, i₀, I₀, Sh, e.trans θ₀, hs, hna, ⟨?_, ?_⟩, hlift, hline, ?_⟩
  · intro φ hφJ hφ
    have hφ'J : u⁻¹ * φ * u ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hu) hφJ) hu
    obtain ⟨φ₀, hφ₀I₀, hφ₀⟩ := hgeom.1 _ hφ'J (ggConj_commute_line hφ)
    refine ⟨φ₀, hφ₀I₀, fun g hg => ?_⟩
    rw [hres φ hφ g hg, hres' g hg]
    exact hφ₀ (u⁻¹ g) _
  · intro φ hφJ hφ hfixpt
    have hφ'J : u⁻¹ * φ * u ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hu) hφJ) hu
    have hfixpt' : ∀ g ∈ ggFixDer f, (u⁻¹ * φ * u) g = g := by
      intro g hg
      have hgx : u g ∈ ggFixDer (u * f * u⁻¹) := by
        rw [ggFixDer_conj_mem]
        simpa using hg
      have h1 := hfixpt (u g) hgx
      simp [MulAut.mul_apply, h1]
    have h1 : u⁻¹ * φ * u = 1 := hgeom.2 _ hφ'J (ggConj_commute_line hφ) hfixpt'
    calc φ = u * (u⁻¹ * φ * u) * u⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro φ hφJ hφ φ₀ hφ₀Sh hφ₀ hcycφ
    have hφ'J : u⁻¹ * φ * u ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hu) hφJ) hu
    have hφ'₀ : ∀ (g : R) (hg : g ∈ ggFixDer f),
        θ₀ ⟨(u⁻¹ * φ * u) g, ggFixDer_map_mem (ggConj_commute_line hφ) hg⟩ =
          φ₀ (θ₀ ⟨g, hg⟩) := by
      intro g hg
      have hgx : u g ∈ ggFixDer (u * f * u⁻¹) := by
        rw [ggFixDer_conj_mem]
        simpa using hg
      have h1 := hφ₀ (u g) hgx
      rw [hres φ hφ (u g) hgx, hres' (u g) hgx] at h1
      have e1 : (⟨(u⁻¹ * φ * u) (u⁻¹ (u g)), ggFixDer_map_mem (ggConj_commute_line hφ)
          ((ggFixDer_conj_mem f u (u g)).1 hgx)⟩ : ggFixDer f) =
          ⟨(u⁻¹ * φ * u) g, ggFixDer_map_mem (ggConj_commute_line hφ) hg⟩ :=
        Subtype.ext (by simp)
      have e2 : (⟨u⁻¹ (u g), (ggFixDer_conj_mem f u (u g)).1 hgx⟩ : ggFixDer f) = ⟨g, hg⟩ :=
        Subtype.ext (by simp)
      rw [e1, e2] at h1
      exact h1
    exact (hX _ hφ'J (ggConj_commute_line hφ) φ₀ hφ₀Sh hφ'₀) (ggFixCompCyclic_conj u hcycφ)

@[expose] def GGRawFieldFixSh (p r : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ f ∈ F, orderOf f = p → GGFixDataSh p r I f

theorem ggRawFieldFixSh_all {p r : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hconj : GGRawFieldConj p R I F) (hnorm : GGRawFieldNorm R I F) (hcyc : GGRawFieldCycW p R I F)
    (h : GGRawFieldFixSh p r R I F) (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a) :
    ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataSh p r I x := by
  intro x hx hxI hxp
  obtain ⟨J, -, hJ, -, -, -, -⟩ := hcyc hs hna
  subst I
  obtain ⟨u, hu, f, hf, rfl⟩ := ggClosure_union_eq_mul hnorm x hx
  obtain ⟨f', hf', u', hu', hf'p, he⟩ := hconj hs hna u hu f hf hxI hxp
  rw [he]
  exact ggFixDataSh_conj hu' (h hs hna f' hf' hf'p)

end CFSG.StandardType
