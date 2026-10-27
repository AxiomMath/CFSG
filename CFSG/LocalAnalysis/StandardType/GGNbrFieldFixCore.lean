module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLift
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggInduced_conj {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R) (n l : L') :
    MulAut.conj (ψ n) (ψ l) = ψ (MulAut.conj n l) := by
  simp [MulAut.conj_apply]

theorem ggInduced_conj_mul_conj_inv {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R) (n : L')
    {a : MulAut L'} {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l)) (l : L') :
    (MulAut.conj (ψ n) * φ * (MulAut.conj (ψ n))⁻¹) (ψ l) =
      ψ ((MulAut.conj n * a * (MulAut.conj n)⁻¹) l) := by
  simp only [MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply, map_mul, map_inv]
  simp only [← h]

theorem ggTorusNoLineFieldComp_of_fixData {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r) {R : Type}
    [Group R] {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hin : GGTorusNoLineComp p r R I)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixData p r I x) :
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
      le_trans (Nat.pow_le_pow_right hp.pos (Nat.le_succ r)) hcard1
    obtain ⟨W, h1, h2⟩ := hin L' ψ hψ hker hperf A hAe hind hc1 hcard3 hsc
    exact ⟨W, h1, fun hN' a₀ ha₀ hne _ hcl => h2 hN' a₀ ha₀ hne hcl⟩
  · obtain ⟨b, hbA, hbA₀⟩ := SetLike.not_le_iff_exists.mp hAA₀
    set x : MulAut R := Ind ⟨b, hbA⟩ with hx
    have hxcl : x ∈ Subgroup.closure (I ∪ F) := hIndcl _
    have hxI : x ∉ I := fun h => hbA₀ ((hmem ⟨b, hbA⟩).mpr ((hIJ _).mp h))
    obtain ⟨R₀, _, I₀, θ₀, hs₀, hna₀, hgeom, -, hline₀⟩ := hfix x hxcl hxI (hIndp _)
    have hK : ⁅ggFixDer x, ggFixDer x⁆ = ggFixDer x := ggFixDer_perfect θ₀ hs₀ hna₀
    obtain ⟨ψ'', hψ''eq, hψ''s, -, hψ''kc, hψ''perf⟩ :=
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
    generalize ggCore ψ (ggFixDer x) = H at hmapK hHK hstab hbH ψ'' hψ''eq hψ''s hψ''kc hψ''perf
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
    have hcardA₀ : p ^ r ≤ Nat.card A₀ := by
      have h : p * p ^ r ≤ p * Nat.card A₀ :=
        calc p * p ^ r = p ^ (r + 1) := by ring
          _ ≤ Nat.card A := hcard1
          _ ≤ p * Nat.card A₀ := hcardle
      exact Nat.le_of_mul_le_mul_left h hp.pos
    have hcardB₀ : Nat.card res.range = Nat.card A₀ :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have hp3 : p ^ 3 ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr
    have hsc₀ := ggTransfer_selfCent res hres hdec hsc hconj
    obtain ⟨W₀, h1, h2⟩ := hline₀ H ψ'' hψ''s hψ''kc hψ''perf res.range
      (ggIsElemAbelian_range hA₀A hAe res) hB₀ind (hcardB₀ ▸ hcardA₀)
      (hcardB₀ ▸ hp3.trans hcardA₀) hsc₀
    refine ⟨Subtype.val '' W₀, ggTransfer_first res hres hdec h1, ?_⟩
    intro hN' a₀ ha₀ hne hind _
    have ha₀A₀ : a₀ ∈ A₀ := by
      obtain ⟨φ, hφ, h⟩ := hind
      have e := ggInduced_unique hψ (hInd ⟨a₀, ha₀⟩) h
      exact (hmem ⟨a₀, ha₀⟩).mpr (by rw [e]; exact (hIJ _).mp hφ)
    exact ggTransfer_second res hres hinj hA₀A hnorm h2 hN' a₀ ha₀A₀ hne

theorem ggTorusFieldTransfer {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hin : GGTorusNoLineComp p r R I)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixData p r I x) :
    GGTorusLiftFix p r R I F ∧ GGTorusNoLineFieldComp p r R I F :=
  ⟨ggTorusLiftFix_of_fixData hfix, ggTorusNoLineFieldComp_of_fixData hp hr hInn hin hcyc hfix⟩

end CFSG.StandardType

end
