module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreTwo
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGCenterKp (Kp : ℕ → Prop) (R : Type) [Group R] : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Kp (Nat.card ψ.ker)

@[expose] def GGTorusNoLineTwoKX (p : ℕ) (Kp : ℕ → Prop) (R : Type) [Group R]
    (I X : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Kp (Nat.card ψ.ker) →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 2 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ((∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ X, ∀ l : L', φ (ψ l) = ψ (a₀ l)) ∨
            ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)

@[expose] def GGFixNoCompOn {R : Type} [Group R] (I : Set (MulAut R)) (x : MulAut R) {R₀ : Type}
    [Group R₀] (θ₀ : ggFixDer x ≃* R₀) (X₀ : Set (MulAut R₀)) : Prop :=
  ∀ φ ∈ I, ∀ hφ : φ * x = x * φ, ∀ φ₀ ∈ X₀,
    (∀ (g : R) (hg : g ∈ ggFixDer x), θ₀ ⟨φ g, ggFixDer_map_mem hφ hg⟩ = φ₀ (θ₀ ⟨g, hg⟩)) →
      ∀ J : Subgroup R, ¬ IsComponentOf J (ggFix φ)

@[expose] def GGFixDataKX (p : ℕ) (Kp : ℕ → Prop) {R : Type} [Group R] (I : Set (MulAut R))
    (x : MulAut R) : Prop :=
  ∃ (R₀ : Type) (_ : Group R₀) (I₀ X₀ : Set (MulAut R₀)) (θ₀ : ggFixDer x ≃* R₀),
    IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ GGFixGeom I x I₀ θ₀ ∧
      GGTorusLift p 0 R₀ ∧ GGTorusNoLineTwoKX p Kp R₀ I₀ X₀ ∧ GGFixNoCompOn I x θ₀ X₀

theorem not_ggFixCompCyclic_of_noComp {p : ℕ} {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {φ : MulAut R} (hc : ∀ l, φ (ψ l) = ψ (a l))
    (h : ∀ J : Subgroup R, ¬ IsComponentOf J (ggFix φ)) : ¬ GGFixCompCyclic p a := by
  rintro ⟨J₁, hJ₁, -⟩
  exact h _ (USixTwo.isComponentOf_map_fix hψ hker hc hJ₁)

theorem ggTorusLiftFix_of_fixDataKX {p : ℕ} {Kp : ℕ → Prop} {R : Type} [Group R]
    {I F : Set (MulAut R)}
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataKX p Kp I x) :
    GGTorusLiftFix p 0 R I F := by
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

section Transfer

variable {L' : Type} [Group L'] {A A₀ : Subgroup (MulAut L')} {H : Subgroup L'}

theorem ggTransfer_secondX (res : A₀ →* MulAut H)
    (hres : ∀ (a : A₀) (l : H), ((res a l : H) : L') = (a : MulAut L') l)
    (hinj : Function.Injective res) (hA₀ : A₀ ≤ A)
    (hnorm : ∀ n ∈ H, ∀ a ∈ A₀, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A →
      MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A₀) {W₀ : Set H} {Q : MulAut H → Prop}
    (h2 : (∀ n ∈ W₀, ∀ a ∈ res.range, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ res.range) →
      ∀ a₀ ∈ res.range, a₀ ≠ 1 → Q a₀ ∨
        ∃ n ∈ W₀, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀) :
    (∀ n ∈ (Subtype.val '' W₀ : Set L'), ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
      ∀ (a₀ : MulAut L') (ha₀ : a₀ ∈ A₀), a₀ ≠ 1 → Q (res ⟨a₀, ha₀⟩) ∨
        ∃ n ∈ (Subtype.val '' W₀ : Set L'),
          MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀ := by
  intro hN a₀ ha₀ ha₀ne
  have h2hyp : ∀ n ∈ W₀, ∀ a ∈ res.range,
      MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ res.range := by
    intro n hnW a ha
    obtain ⟨a', rfl⟩ := ha
    have hAN : MulAut.conj (n : L') * (a' : MulAut L')
        * (MulAut.conj (n : L'))⁻¹ ∈ A :=
      hN (n : L') ⟨n, hnW, rfl⟩ (a' : MulAut L') (hA₀ a'.2)
    have hA₀N : MulAut.conj (n : L') * (a' : MulAut L')
        * (MulAut.conj (n : L'))⁻¹ ∈ A₀ :=
      hnorm (n : L') n.2 a' a'.2 hAN
    let c : A₀ :=
      ⟨MulAut.conj (n : L') * (a' : MulAut L') * (MulAut.conj (n : L'))⁻¹, hA₀N⟩
    exact ⟨c, ggRestrict_conj res hres n a' c rfl⟩
  have hne : res ⟨a₀, ha₀⟩ ≠ 1 := by
    intro h
    apply ha₀ne
    have h1 : (⟨a₀, ha₀⟩ : A₀) = 1 := hinj (h.trans (map_one res).symm)
    simpa using congrArg Subtype.val h1
  rcases h2 h2hyp (res ⟨a₀, ha₀⟩) ⟨⟨a₀, ha₀⟩, rfl⟩ hne with hQ | ⟨n₀, hn₀W, hn₀bad⟩
  · exact Or.inl hQ
  refine Or.inr ⟨(n₀ : L'), ⟨n₀, hn₀W, rfl⟩, ?_⟩
  intro h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  let c : A₀ := (⟨a₀, ha₀⟩ : A₀) ^ m
  have hc : (c : MulAut L') =
      MulAut.conj (n₀ : L') * a₀ * (MulAut.conj (n₀ : L'))⁻¹ := by
    change (↑(((⟨a₀, ha₀⟩ : A₀) ^ m)) : MulAut L') =
      MulAut.conj (n₀ : L') * a₀ * (MulAut.conj (n₀ : L'))⁻¹
    rw [Subgroup.coe_zpow]
    exact hm
  have hr := ggRestrict_conj res hres n₀ ⟨a₀, ha₀⟩ c hc
  apply hn₀bad
  rw [← hr]
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, (map_zpow res ⟨a₀, ha₀⟩ m).symm⟩

end Transfer

theorem ggTorusNoLineFieldComp_of_fixDataKX {p : ℕ} {Kp : ℕ → Prop} (hp : p.Prime) {R : Type}
    [Group R] {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hin : GGTorusNoLineComp p 0 R I) (hKp : GGCenterKp Kp R)
    (hKdvd : ∀ a b : ℕ, a ∣ b → Kp b → Kp a)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataKX p Kp I x) :
    GGTorusNoLineFieldComp p 0 R I F := by
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
    have hc1 : p ^ 0 ≤ Nat.card A :=
      le_trans (Nat.pow_le_pow_right hp.pos (Nat.zero_le 1)) hcard1
    obtain ⟨W, h1, h2⟩ := hin L' ψ hψ hker hperf A hAe hind hc1 hcard3 hsc
    exact ⟨W, h1, fun hN' a₀ ha₀ hne _ hcl => h2 hN' a₀ ha₀ hne hcl⟩
  · obtain ⟨b, hbA, hbA₀⟩ := SetLike.not_le_iff_exists.mp hAA₀
    set x : MulAut R := Ind ⟨b, hbA⟩ with hx
    have hxcl : x ∈ Subgroup.closure (I ∪ F) := hIndcl _
    have hxI : x ∉ I := fun h => hbA₀ ((hmem ⟨b, hbA⟩).mpr ((hIJ _).mp h))
    obtain ⟨R₀, _, I₀, X₀, θ₀, hs₀, hna₀, hgeom, -, hline₀, hX⟩ :=
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
    have hKpH : Kp (Nat.card ψ''.ker) := by
      let e : ψ''.ker →* ψ.ker :=
        { toFun := fun k => ⟨((k : H) : L'), (hψ''i (k : H)).mp k.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have he : Function.Injective e := fun k k' h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : ψ.ker => (z : L')) h))
      exact hKdvd _ _ (Subgroup.card_dvd_of_injective e he) (hKp L' ψ hψ hker hperf)
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
    have h2₀ : p ^ 2 ≤ Nat.card res.range := by
      rw [hcardB₀]
      have h : p * p ^ 2 ≤ p * Nat.card A₀ :=
        calc p * p ^ 2 = p ^ 3 := by ring
          _ ≤ Nat.card A := hcard3
          _ ≤ p * Nat.card A₀ := hcardle
      exact Nat.le_of_mul_le_mul_left h hp.pos
    obtain ⟨W₀, h1, h2⟩ := hline₀ H ψ'' hψ''s hψ''kc hψ''p hKpH res.range
      (ggIsElemAbelian_range hA₀A hAe res) hB₀ind h2₀ hsc₀
    refine ⟨Subtype.val '' W₀, ggTransfer_first res hres hdec h1, ?_⟩
    intro hN' a₀ ha₀ hne hind hcl
    have ha₀A₀ : a₀ ∈ A₀ := by
      obtain ⟨φ, hφ, h⟩ := hind
      have e := ggInduced_unique hψ (hInd ⟨a₀, ha₀⟩) h
      exact (hmem ⟨a₀, ha₀⟩).mpr (by rw [e]; exact (hIJ _).mp hφ)
    rcases ggTransfer_secondX res hres hinj hA₀A hnorm
        (Q := fun a => ∃ φ ∈ X₀, ∀ l : H, φ (ψ'' l) = ψ'' (a l)) h2 hN' a₀ ha₀A₀ hne with
      ⟨φ₀, hφ₀X, hφ₀⟩ | hmove
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
      exact not_ggFixCompCyclic_of_noComp hψ hker (hInd ⟨a₀, ha₀⟩)
        (hX φ hφI hφx φ₀ hφ₀X hrestr) hcl
    · exact hmove

theorem ggTorusFieldTransferKX {p : ℕ} {Kp : ℕ → Prop} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hin : GGTorusNoLineComp p 0 R I) (hKp : GGCenterKp Kp R)
    (hKdvd : ∀ a b : ℕ, a ∣ b → Kp b → Kp a)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataKX p Kp I x) :
    GGTorusLiftFix p 0 R I F ∧ GGTorusNoLineFieldComp p 0 R I F :=
  ⟨ggTorusLiftFix_of_fixDataKX hfix,
    ggTorusNoLineFieldComp_of_fixDataKX hp hInn hin hKp hKdvd hcyc hfix⟩

theorem ggConj_commute_line {R : Type} [Group R] {φ f u : MulAut R}
    (hφ : φ * (u * f * u⁻¹) = (u * f * u⁻¹) * φ) : (u⁻¹ * φ * u) * f = f * (u⁻¹ * φ * u) :=
  calc u⁻¹ * φ * u * f = u⁻¹ * (φ * (u * f * u⁻¹)) * u := by group
    _ = u⁻¹ * ((u * f * u⁻¹) * φ) * u := by rw [hφ]
    _ = f * (u⁻¹ * φ * u) := by group

theorem ggFix_conj_eq_map {R : Type} [Group R] (φ u : MulAut R) :
    ggFix (u⁻¹ * φ * u) = (ggFix φ).map (u⁻¹ : MulAut R).toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨u g, ?_, by simp⟩
    change φ (u g) = u g
    have h : (u⁻¹ * φ * u) g = g := hg
    simp only [MulAut.mul_apply] at h
    have h' := congrArg u h
    simpa using h'
  · rintro ⟨g', hg', rfl⟩
    change (u⁻¹ * φ * u) (u⁻¹ g') = u⁻¹ g'
    have h : φ g' = g' := hg'
    simp [MulAut.mul_apply, h]

theorem ggFixDataKX_conj {p : ℕ} {Kp : ℕ → Prop} {R : Type} [Group R]
    {J : Subgroup (MulAut R)} {f u : MulAut R} (hu : u ∈ J)
    (h : GGFixDataKX p Kp (J : Set (MulAut R)) f) :
    GGFixDataKX p Kp (J : Set (MulAut R)) (u * f * u⁻¹) := by
  obtain ⟨R₀, i₀, I₀, X₀, θ₀, hs, hna, hgeom, hlift, hline, hX⟩ := h
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
  refine ⟨R₀, i₀, I₀, X₀, e.trans θ₀, hs, hna, ⟨?_, ?_⟩, hlift, hline, ?_⟩
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
  · intro φ hφJ hφ φ₀ hφ₀X hφ₀ J' hJ'
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
    apply hX _ hφ'J (ggConj_commute_line hφ) φ₀ hφ₀X hφ'₀ (J'.map (u⁻¹ : MulAut R).toMonoidHom)
    rw [ggFix_conj_eq_map]
    exact ⟨Subgroup.map_mono hJ'.1, IsSubnormal.map _ hJ'.2.1,
      Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective J' _ (u⁻¹ : MulAut R).injective).symm hJ'.2.2⟩

@[expose] def GGRawFieldFixKX (p : ℕ) (Kp : ℕ → Prop) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ f ∈ F, orderOf f = p → GGFixDataKX p Kp I f

theorem ggRawFieldFixKX_all {p : ℕ} {Kp : ℕ → Prop} {R : Type} [Group R]
    {I F : Set (MulAut R)} (hconj : GGRawFieldConj p R I F) (hnorm : GGRawFieldNorm R I F)
    (hcyc : GGRawFieldCycW p R I F) (h : GGRawFieldFixKX p Kp R I F) (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) :
    ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataKX p Kp I x := by
  intro x hx hxI hxp
  obtain ⟨J, -, hJ, -, -, -, -⟩ := hcyc hs hna
  subst I
  obtain ⟨u, hu, f, hf, rfl⟩ := ggClosure_union_eq_mul hnorm x hx
  obtain ⟨f', hf', u', hu', hf'p, he⟩ := hconj hs hna u hu f hf hxI hxp
  rw [he]
  exact ggFixDataKX_conj hu' (h hs hna f' hf' hf'p)

theorem largeEvenLabelAll_fieldKLevelComp_of_fixKX {p : ℕ} {Kp : ℕ → Prop} (hp : p.Prime)
    (hKdvd : ∀ a b : ℕ, a ∣ b → Kp b → Kp a) {lab : LargeEvenLabel}
    (hRow : LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧
      GGTorusLift p 0 R ∧ (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusNoLineComp p 0 R I ∧ GGCenterKp Kp R))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hconj : LargeEvenLabelAll lab (GGRawFieldConj p))
    (hcen : LargeEvenLabelAll lab GGRawFieldCentral)
    (hinn : LargeEvenLabelAll lab (GGRawInnField p))
    (hstd : LargeEvenLabelAll lab (GGRawFieldFixKX p Kp)) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  refine (largeEvenLabelAll_and hRow (largeEvenLabelAll_and hcyc (largeEvenLabelAll_and hconj
    (largeEvenLabelAll_and hcen (largeEvenLabelAll_and hinn hstd))))).mono ?_
  rintro R _ I F ⟨⟨hi, hl, hn⟩, hcy, hc, hce, hin, hst⟩ hs hna
  obtain ⟨hin0, hKp⟩ := hn hs hna
  have hfix := ggRawFieldFixKX_all hc (ggRawFieldNorm_of_central hce hin hs hna) hcy hst hs hna
  obtain ⟨hLF, hNF⟩ := ggTorusFieldTransferKX hp hi hin0 hKp hKdvd (hcy hs hna) hfix
  exact ⟨hi, 0, hl, hLF, hin0, hNF⟩

theorem ggFieldKLevel_of_fixKX {Kp : ℕ → ℕ → Prop} {S : ℕ → LargeEvenLabel → Prop}
    (hKdvd : ∀ p a b : ℕ, a ∣ b → Kp p b → Kp p a)
    (hNot : ∀ p lab, S p lab → GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3))
    (hRow : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧
        GGTorusLift p 0 R ∧ (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
          GGTorusNoLineComp p 0 R I ∧ GGCenterKp (Kp p) R))
    (hFix : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (GGRawFieldFixKX p (Kp p)))
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hS
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab (hNot p lab hS).1).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  exact largeEvenLabelAll_fieldKLevelComp_of_fixKX hp (hKdvd p) (hRow p lab hp hp2 hlab hS) hCyc
    (hconj p hp hp2 lab hlab (hNot p lab hS).2) (hcen lab hlab) (hinn p hp hp2 lab hlab)
    (hFix p lab hp hp2 hlab hS)

end CFSG.StandardType

end
