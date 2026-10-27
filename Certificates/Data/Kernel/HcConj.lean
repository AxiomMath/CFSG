module

public import Certificates.Data.Kernel.HcPack

public section

namespace CFSG.KC.HcPack

section Gen

variable {α γ : Type} [BEq α]

@[expose] def cjAdd (f h : γ → α → α) (p : α × α) (acc : List (α × α) × List (α × α)) (kb : γ) :
    List (α × α) × List (α × α) :=
  let x' := f kb p.1
  if acc.1.any (fun q => q.1 == x') then acc else
    let q' := (x', h kb p.2)
    (acc.1 ++ [q'], acc.2 ++ [q'])

@[expose] def cjStepG (f h : γ → α → α) (gs : List γ) (seen fr : List (α × α)) :
    List (α × α) × List (α × α) :=
  fr.foldl (fun acc p => gs.foldl (cjAdd f h p) acc) (seen, [])

@[expose] def cjAuxG (f h : γ → α → α) (gs : List γ) :
    ℕ → List (α × α) → List (α × α) → List (α × α)
  | 0, seen, _ => seen
  | n + 1, seen, fr =>
    if fr.isEmpty then seen else
      let r := cjStepG f h gs seen fr
      cjAuxG f h gs n r.1 r.2

end Gen

@[expose] noncomputable def conjP (ab : ℕ × ℕ) (x : ℕ) : ℕ := mulP (mulP ab.1 x) ab.2

@[expose] noncomputable def conjCP (ab : ℕ × ℕ) (c : ℕ) : ℕ := mulP ab.1 c

@[expose] def cjGP : List (ℕ × ℕ) :=
  [(1459489772190472173560349220849168662699482027105, 1459802287035362921683008101000308218513723532291),
    (1459802287035362921683008101000308218513723532291, 1459489772190472173560349220849168662699482027105),
    (1133210907958796891996611681291775908598762440832, 1364122364031551726010219206373941382942136109408),
    (1364122364031551726010219206373941382942136109408, 1133210907958796891996611681291775908598762440832),
    (1459957104930169070366788001133702281052641597602, 1459972453025941830183551456764569644534127395270),
    (1459972453025941830183551456764569644534127395270, 1459957104930169070366788001133702281052641597602),
    (945283157430205989154843984332446948760502770720, 1316887607405542101115088452620304969528701470752),
    (1316887607405542101115088452620304969528701470752, 945283157430205989154843984332446948760502770720),
    (1459746573682848692498805938276209674371466303584, 1459746573682848692498805938276209674371466303584),
    (1459746573682848692498805938276209674371466303584, 1459746573682848692498805938276209674371466303584)]

@[expose] noncomputable def cjClassP (r : ℕ) : List (ℕ × ℕ) :=
  cjAuxG conjP conjCP cjGP 100 [(r, idP)] [(r, idP)]

@[expose] noncomputable def idxC (x i : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih y => Bool.rec (motive := fun _ => ℕ) (Nat.succ (ih (y / 32))) 0 (Nat.beq (y % 32) i))
    n x

@[expose] noncomputable def invP (x : ℕ) : ℕ := pk ((List.range 32).map fun i => idxC x i 32)

@[expose] noncomputable def powP (x : ℕ) : ℕ → ℕ
  | 0 => idP
  | n + 1 => mulP x (powP x n)

end CFSG.KC.HcPack

end
